use serde::{Deserialize, Serialize};

use crate::path::{ExploreConfig, ExploreStrategy};
use crate::state::SymState;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum AddressValue {
    Integer(u64),
    String(String),
}

impl AddressValue {
    pub fn parse(&self) -> Result<u64, String> {
        match self {
            Self::Integer(value) => Ok(*value),
            Self::String(text) => parse_address_text(text),
        }
    }
}

fn parse_address_text(text: &str) -> Result<u64, String> {
    let trimmed = text.trim();
    let has_minus = trimmed.char_indices().skip(1).any(|(_, ch)| ch == '-');
    if trimmed.contains('+') || has_minus {
        return parse_address_expression(trimmed);
    }
    parse_address_atom(trimmed)
}

fn parse_address_expression(text: &str) -> Result<u64, String> {
    let mut expr = text.trim();
    let mut total = if let Some(rest) = expr.strip_prefix('-') {
        expr = rest.trim_start();
        0i128
    } else {
        let (head, tail) = split_next_term(expr);
        expr = tail;
        parse_address_atom(head)? as i128
    };

    while !expr.is_empty() {
        let op = expr
            .chars()
            .next()
            .ok_or_else(|| format!("invalid address expression: {}", text))?;
        if op != '+' && op != '-' {
            return Err(format!("invalid address expression: {}", text));
        }
        let remainder = expr[op.len_utf8()..].trim_start();
        let (term, tail) = split_next_term(remainder);
        let value = parse_address_atom(term)? as i128;
        total = if op == '+' {
            total + value
        } else {
            total - value
        };
        expr = tail;
    }

    u64::try_from(total).map_err(|_| format!("address expression underflow/overflow: {}", text))
}

fn split_next_term(text: &str) -> (&str, &str) {
    let mut depth = 0usize;
    for (idx, ch) in text.char_indices() {
        match ch {
            '(' => depth += 1,
            ')' => depth = depth.saturating_sub(1),
            '+' | '-' if depth == 0 && idx > 0 => {
                return (text[..idx].trim_end(), text[idx..].trim_start());
            }
            _ => {}
        }
    }
    (text.trim(), "")
}

fn parse_address_atom(text: &str) -> Result<u64, String> {
    let trimmed = text.trim().trim_matches(|ch| ch == '(' || ch == ')');
    if let Some(hex) = trimmed
        .strip_prefix("0x")
        .or_else(|| trimmed.strip_prefix("0X"))
    {
        return u64::from_str_radix(hex, 16)
            .map_err(|_| format!("invalid hex address: {}", trimmed));
    }
    trimmed
        .parse::<u64>()
        .or_else(|_| u64::from_str_radix(trimmed, 16))
        .map_err(|_| format!("invalid address: {}", trimmed))
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum StartSpec {
    #[default]
    Entry,
    Address {
        addr: AddressValue,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum PredicateSpec {
    Address { addr: AddressValue },
    AddressSet { addrs: Vec<AddressValue> },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(tag = "kind", rename_all = "snake_case")]
pub enum InputSpec {
    Fd {
        fd: i32,
        len: usize,
        #[serde(default)]
        name: Option<String>,
        #[serde(default)]
        alphabet: Option<String>,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct BudgetSpec {
    #[serde(default)]
    pub max_states: Option<usize>,
    #[serde(default)]
    pub max_depth: Option<usize>,
    #[serde(default)]
    pub max_finds: Option<usize>,
    #[serde(default)]
    /// Worklist steps this run may take. Named for work rather than time so a
    /// spec reproduces the same exploration on any machine.
    pub max_steps: Option<u64>,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum StrategySpec {
    #[default]
    Dfs,
    Bfs,
    Random,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq, Default)]
#[serde(rename_all = "snake_case")]
pub enum MergeSpec {
    #[default]
    Off,
    SamePc,
}

fn default_skip_sleep_calls() -> bool {
    true
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct RuntimeSpec {
    #[serde(default)]
    pub tty_fds: Vec<i32>,
    #[serde(default = "default_skip_sleep_calls")]
    pub skip_sleep_calls: bool,
}

impl Default for RuntimeSpec {
    fn default() -> Self {
        Self {
            tty_fds: Vec::new(),
            skip_sleep_calls: default_skip_sleep_calls(),
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct ExplorationSpec {
    #[serde(default)]
    pub start: StartSpec,
    #[serde(default)]
    pub find: Vec<PredicateSpec>,
    #[serde(default)]
    pub avoid: Vec<PredicateSpec>,
    #[serde(default)]
    pub inputs: Vec<InputSpec>,
    #[serde(default)]
    pub budget: BudgetSpec,
    #[serde(default)]
    pub strategy: StrategySpec,
    #[serde(default)]
    pub merge: MergeSpec,
    #[serde(default)]
    pub runtime: RuntimeSpec,
}

impl ExplorationSpec {
    pub fn validate(&self) -> Result<(), String> {
        if self.find.is_empty() {
            return Err("exploration spec requires at least one find predicate".to_string());
        }
        for input in &self.inputs {
            match input {
                InputSpec::Fd {
                    len,
                    alphabet,
                    name,
                    ..
                } => {
                    if *len == 0 {
                        return Err("fd input length must be greater than zero".to_string());
                    }
                    if let Some(alphabet) = alphabet
                        && alphabet.is_empty()
                    {
                        return Err("fd input alphabet must not be empty".to_string());
                    }
                    if let Some(name) = name
                        && name.trim().is_empty()
                    {
                        return Err("fd input name must not be empty".to_string());
                    }
                }
            }
        }
        let _ = self.find_addresses()?;
        let _ = self.avoid_addresses()?;
        Ok(())
    }

    pub fn start_pc(&self, entry_pc: u64) -> Result<u64, String> {
        match &self.start {
            StartSpec::Entry => Ok(entry_pc),
            StartSpec::Address { addr } => addr.parse(),
        }
    }

    pub fn max_finds(&self) -> usize {
        self.budget.max_finds.unwrap_or(1).max(1)
    }

    pub fn to_explore_config(&self, defaults: &ExploreConfig) -> ExploreConfig {
        let mut config = defaults.clone();
        if let Some(max_states) = self.budget.max_states {
            config.max_states = max_states;
        }
        if let Some(max_depth) = self.budget.max_depth {
            config.max_depth = max_depth;
        }
        if let Some(max_steps) = self.budget.max_steps {
            config.max_steps = Some(max_steps);
        }
        config.strategy = match self.strategy {
            StrategySpec::Dfs => ExploreStrategy::Dfs,
            StrategySpec::Bfs => ExploreStrategy::Bfs,
            StrategySpec::Random => ExploreStrategy::Random,
        };
        config.merge_states = matches!(self.merge, MergeSpec::SamePc);
        config
    }

    pub fn find_addresses(&self) -> Result<Vec<u64>, String> {
        flatten_predicates(&self.find)
    }

    pub fn avoid_addresses(&self) -> Result<Vec<u64>, String> {
        flatten_predicates(&self.avoid)
    }

    pub fn apply_to_state<'ctx>(&self, state: &mut SymState<'ctx>) {
        for fd in &self.runtime.tty_fds {
            state.set_tty_fd(*fd, true);
        }
        state.set_skip_sleep_calls(self.runtime.skip_sleep_calls);
        for input in &self.inputs {
            match input {
                InputSpec::Fd {
                    fd,
                    len,
                    name,
                    alphabet,
                } => {
                    let default_name = format!("fd{}_input", fd);
                    state.add_symbolic_fd_input(
                        *fd,
                        *len,
                        name.as_deref().unwrap_or(&default_name),
                        alphabet.as_deref(),
                    );
                }
            }
        }
    }
}

fn flatten_predicates(predicates: &[PredicateSpec]) -> Result<Vec<u64>, String> {
    let mut out = Vec::new();
    for predicate in predicates {
        match predicate {
            PredicateSpec::Address { addr } => out.push(addr.parse()?),
            PredicateSpec::AddressSet { addrs } => {
                for addr in addrs {
                    out.push(addr.parse()?);
                }
            }
        }
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_hex_addresses() {
        assert_eq!(
            AddressValue::String("0x401000".to_string())
                .parse()
                .unwrap(),
            0x401000
        );
    }

    #[test]
    fn parses_simple_address_expressions() {
        assert_eq!(
            AddressValue::String("0x401000 + 0x20 - 4".to_string())
                .parse()
                .unwrap(),
            0x40101c
        );
    }

    #[test]
    fn validates_fd_inputs() {
        let spec = ExplorationSpec {
            find: vec![PredicateSpec::Address {
                addr: AddressValue::Integer(0x401000),
            }],
            inputs: vec![InputSpec::Fd {
                fd: 0,
                len: 4,
                name: Some("stdin".to_string()),
                alphabet: Some("abcd".to_string()),
            }],
            ..Default::default()
        };
        assert!(spec.validate().is_ok());
    }

    #[test]
    fn rejects_empty_find_list() {
        let spec = ExplorationSpec::default();
        assert!(spec.validate().is_err());
    }
}

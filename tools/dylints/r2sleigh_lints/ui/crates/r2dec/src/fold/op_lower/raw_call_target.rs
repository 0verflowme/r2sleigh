use std::collections::BTreeMap;

struct Context;
struct Request<'a> {
    direct_target_context: Option<&'a Context>,
}
#[derive(Clone)]
struct CalleeFacts {
    map: BTreeMap<String, usize>,
}

struct Policy {
    callee_facts: BTreeMap<String, usize>,
    nested: CalleeFacts,
}

struct NestedPolicy {
    callee_facts: CalleeFacts,
}

impl Context {
    fn prepared_constish_target_addr(&self) -> Option<u64> {
        Some(0)
    }

    fn is_import_policy_authorized(&self) -> bool {
        true
    }

    fn identity_for_callsite(&self) -> Option<u64> {
        Some(0)
    }

    fn summary_helper_view_for_name(&self) -> Option<u64> {
        Some(0)
    }
}

fn extract_call_address(_: &str) -> Option<u64> {
    Some(0)
}

fn is_modeled_callee_identity() -> bool {
    true
}

fn modeled_callee_addr_for_identity() -> Option<u64> {
    Some(0)
}

fn main() {
    let ctx = Context;
    let name = "ram:401000";
    let mut policy = Policy {
        callee_facts: BTreeMap::new(),
        nested: CalleeFacts {
            map: BTreeMap::new(),
        },
    };
    let mut nested_policy = NestedPolicy {
        callee_facts: CalleeFacts {
            map: BTreeMap::new(),
        },
    };
    policy.callee_facts.insert("printf".to_string(), 2);
    policy.nested.map.insert("puts".to_string(), 1);
    nested_policy
        .callee_facts
        .map
        .insert("scanf".to_string(), 3);
    let _ = ctx.prepared_constish_target_addr();
    let _ = extract_call_address(name);
    let _ = is_modeled_callee_identity();
    let _ = modeled_callee_addr_for_identity();
    let _ = ctx.is_import_policy_authorized();
    let _ = ctx.identity_for_callsite();
    let _ = ctx.summary_helper_view_for_name();
    let _ = name.strip_prefix("ram:");
    let _ = name.strip_prefix("tmp:");
    let _ = policy.callee_facts.contains_key("printf");
    let _ = policy.callee_facts.clone().contains_key("printf");
    let _ = (&policy.callee_facts).contains_key("printf");
    let _ = policy.nested.map.contains_key("puts");
    let _ = nested_policy.callee_facts.map.contains_key("scanf");
    let _ = Request {
        direct_target_context: Some(&ctx),
    };
    let _ = Request {
        direct_target_context: None,
    };
}

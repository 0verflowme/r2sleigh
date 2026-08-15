//! r2sleigh CLI - Compile Sleigh specs to r2il
//!
//! Usage:
//!   r2sleigh compile <input.slaspec> -o <output.r2il>
//!   r2sleigh info <input.r2il>
//!   r2sleigh test-arch <arch>
//!   r2sleigh disasm --arch x86-64 --bytes "554889e5"

#[cfg(feature = "sleigh-config")]
use clap::ValueEnum;
use clap::{Parser, Subcommand};
use r2il::{serialize, validate_archspec};
use r2sleigh_lift::{
    Lifter, create_arm_spec, create_riscv32_spec, create_riscv64_spec, create_x86_64_spec,
};
use std::path::{Path, PathBuf};

#[cfg(feature = "sleigh-config")]
use r2sleigh_export::{
    ExportFormat, InstructionAction, InstructionExportInput, export_instruction,
};
#[cfg(feature = "sleigh-config")]
use r2sleigh_lift::{Disassembler, build_arch_spec, userop_map_for_arch};

/// r2sleigh - Sleigh to r2il compiler for radare2
#[derive(Parser)]
#[command(name = "r2sleigh")]
#[command(author, version, about, long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand)]
enum Commands {
    /// Compile a Sleigh specification to r2il binary format
    Compile {
        /// Input Sleigh specification file (.slaspec)
        input: PathBuf,

        /// Output r2il binary file
        #[arg(short, long)]
        output: Option<PathBuf>,

        /// Architecture variant (e.g., "default", "thumb")
        #[arg(short, long, default_value = "default")]
        variant: String,
    },

    /// Display information about an r2il file
    Info {
        /// Input r2il file
        input: PathBuf,

        /// Show all registers
        #[arg(short, long)]
        registers: bool,

        /// Show all address spaces
        #[arg(short, long)]
        spaces: bool,
    },

    /// Generate a test architecture specification
    TestArch {
        /// Architecture name (x86-64, arm, mips32be, mips32le, riscv64, riscv32)
        arch: String,

        /// Output r2il binary file
        #[arg(short, long)]
        output: Option<PathBuf>,
    },

    /// Show version and format information
    Version,

    /// Disassemble instruction bytes to r2il
    #[cfg(feature = "sleigh-config")]
    Disasm {
        /// Architecture (e.g., x86-64, ARM)
        #[arg(short, long)]
        arch: String,

        /// Hex-encoded instruction bytes
        #[arg(short, long)]
        bytes: String,

        /// Base address for disassembly
        #[arg(long, default_value = "0x1000")]
        addr: String,

        /// Output format: text, json, esil, or r2cmd
        #[arg(short, long, default_value = "text")]
        format: String,
    },

    /// Run a one-liner analysis action on one lifted instruction
    #[cfg(feature = "sleigh-config")]
    Run {
        /// Architecture (e.g., x86-64, ARM)
        #[arg(short, long)]
        arch: String,

        /// Hex-encoded instruction bytes
        #[arg(short, long)]
        bytes: String,

        /// Base address for disassembly
        #[arg(long, default_value = "0x1000")]
        addr: String,

        /// Action: lift, ssa, defuse, dec
        #[arg(long, value_enum)]
        action: RunActionArg,

        /// Output format for the selected action
        #[arg(short, long, value_enum)]
        format: RunFormatArg,
    },
}

#[cfg(feature = "sleigh-config")]
#[derive(Clone, Copy, Debug, ValueEnum)]
enum RunActionArg {
    Lift,
    Ssa,
    Defuse,
    #[cfg(feature = "decompile")]
    Dec,
}

#[cfg(feature = "sleigh-config")]
impl From<RunActionArg> for InstructionAction {
    fn from(value: RunActionArg) -> Self {
        match value {
            RunActionArg::Lift => InstructionAction::Lift,
            RunActionArg::Ssa => InstructionAction::Ssa,
            RunActionArg::Defuse => InstructionAction::Defuse,
            #[cfg(feature = "decompile")]
            RunActionArg::Dec => InstructionAction::Dec,
        }
    }
}

#[cfg(feature = "sleigh-config")]
#[derive(Clone, Copy, Debug, ValueEnum)]
enum RunFormatArg {
    Json,
    Text,
    Esil,
    #[cfg(feature = "decompile")]
    #[value(name = "c_like")]
    CLike,
    #[value(name = "r2cmd")]
    R2Cmd,
}

#[cfg(feature = "sleigh-config")]
impl From<RunFormatArg> for ExportFormat {
    fn from(value: RunFormatArg) -> Self {
        match value {
            RunFormatArg::Json => ExportFormat::Json,
            RunFormatArg::Text => ExportFormat::Text,
            RunFormatArg::Esil => ExportFormat::Esil,
            #[cfg(feature = "decompile")]
            RunFormatArg::CLike => ExportFormat::CLike,
            RunFormatArg::R2Cmd => ExportFormat::R2Cmd,
        }
    }
}

fn main() {
    let cli = Cli::parse();

    let result = match cli.command {
        Commands::Compile {
            input,
            output,
            variant,
        } => cmd_compile(&input, output.as_ref(), &variant),

        Commands::Info {
            input,
            registers,
            spaces,
        } => cmd_info(&input, registers, spaces),

        Commands::TestArch { arch, output } => cmd_test_arch(&arch, output.as_ref()),

        Commands::Version => cmd_version(),

        #[cfg(feature = "sleigh-config")]
        Commands::Disasm {
            arch,
            bytes,
            addr,
            format,
        } => cmd_disasm(&arch, &bytes, &addr, &format),

        #[cfg(feature = "sleigh-config")]
        Commands::Run {
            arch,
            bytes,
            addr,
            action,
            format,
        } => cmd_run(&arch, &bytes, &addr, action.into(), format.into()),
    };

    if let Err(e) = result {
        eprintln!("Error: {}", e);
        std::process::exit(1);
    }
}

fn cmd_compile(input: &Path, output: Option<&PathBuf>, _variant: &str) -> Result<(), String> {
    println!("Compiling: {}", input.display());

    // Determine output path
    let output_path = match output {
        Some(p) => p.clone(),
        None => input.with_extension("r2il"),
    };

    // Determine architecture from filename
    let arch_name = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("unknown");

    // Create spec based on architecture detection
    // Note: For raw .slaspec files, use sleigh-compiler to compile first.
    // This command works best with pre-built specs.
    let arch_name_lower = arch_name.to_lowercase();
    let spec = if arch_name_lower.contains("riscv64") || arch_name_lower.contains("rv64") {
        println!("  Detected RISC-V RV64 architecture");
        create_riscv64_spec()
    } else if arch_name_lower.contains("riscv32") || arch_name_lower.contains("rv32") {
        println!("  Detected RISC-V RV32 architecture");
        create_riscv32_spec()
    } else if arch_name_lower.contains("x86")
        || arch_name_lower.contains("ia")
        || arch_name_lower.contains("amd64")
        || arch_name_lower.contains("x64")
    {
        println!("  Detected x86-64 architecture");
        create_x86_64_spec()
    } else if arch_name_lower.contains("arm") {
        println!("  Detected ARM architecture");
        create_arm_spec()
    } else {
        println!(
            "  Using generic architecture based on filename: {}",
            arch_name
        );
        // Create a minimal spec
        let lifter = Lifter::new(arch_name);
        lifter.compile().map_err(|e| e.to_string())?
    };

    validate_archspec(&spec).map_err(|e| format!("Invalid architecture specification: {}", e))?;

    // Save the compiled spec
    serialize::save(&spec, &output_path).map_err(|e| e.to_string())?;

    println!("Output: {}", output_path.display());
    println!("  Architecture: {}", spec.name);
    println!("  Registers: {}", spec.registers.len());
    println!("  Spaces: {}", spec.spaces.len());

    // Show file size
    if let Ok(metadata) = std::fs::metadata(&output_path) {
        let size = metadata.len();
        if size >= 1024 * 1024 {
            println!("  Size: {:.2} MB", size as f64 / (1024.0 * 1024.0));
        } else if size >= 1024 {
            println!("  Size: {:.2} KB", size as f64 / 1024.0);
        } else {
            println!("  Size: {} bytes", size);
        }
    }

    Ok(())
}

fn cmd_info(input: &Path, show_registers: bool, show_spaces: bool) -> Result<(), String> {
    let spec = serialize::load(input).map_err(|e| e.to_string())?;
    validate_archspec(&spec).map_err(|e| format!("Invalid architecture specification: {}", e))?;
    let (instruction_endianness, memory_endianness) = endianness_info_lines(&spec);

    println!("r2il File: {}", input.display());
    println!("Architecture: {}", spec.name);
    println!("Variant: {}", spec.variant);
    println!("{}", instruction_endianness);
    println!("{}", memory_endianness);
    println!("Address size: {} bytes", spec.addr_size);
    println!("Alignment: {}", spec.alignment);
    println!("Registers: {}", spec.registers.len());
    println!("Address spaces: {}", spec.spaces.len());
    println!("User operations: {}", spec.userops.len());
    println!("Source files: {}", spec.source_files.len());

    if show_spaces || !show_registers {
        println!("\nAddress Spaces:");
        for space in &spec.spaces {
            println!(
                "  {:12} addr_size={} word_size={} {}",
                space.name,
                space.addr_size,
                space.word_size,
                if space.is_default { "(default)" } else { "" }
            );
        }
    }

    if show_registers {
        println!("\nRegisters:");
        for reg in &spec.registers {
            let parent_str = reg
                .parent
                .as_ref()
                .map(|p| format!(" (sub of {})", p))
                .unwrap_or_default();
            println!(
                "  {:12} offset=0x{:04x} size={}{}",
                reg.name, reg.offset, reg.size, parent_str
            );
        }
    }

    if !spec.userops.is_empty() {
        println!("\nUser Operations:");
        for userop in &spec.userops {
            println!("  {}: {}", userop.index, userop.name);
        }
    }

    if !spec.source_files.is_empty() {
        println!("\nSource Files:");
        for file in &spec.source_files {
            println!("  {}", file);
        }
    }

    Ok(())
}

fn endianness_info_lines(spec: &r2il::ArchSpec) -> (String, String) {
    let instruction = format!("Instruction endianness: {:?}", spec.instruction_endianness);
    let memory = format!("Memory endianness: {:?}", spec.memory_endianness);
    (instruction, memory)
}

fn cmd_test_arch(arch: &str, output: Option<&PathBuf>) -> Result<(), String> {
    let spec = match arch.to_lowercase().as_str() {
        "x86-64" | "x86_64" | "x64" | "amd64" => {
            println!("Generating x86-64 test specification...");
            create_x86_64_spec()
        }
        "arm" | "arm32" => {
            println!("Generating ARM test specification...");
            create_arm_spec()
        }
        #[cfg(feature = "mips")]
        "mips" | "mips32" | "mips32be" | "mipsbe" | "mipseb" => {
            println!("Generating MIPS32 big-endian test specification...");
            build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            )
            .map_err(|e| e.to_string())?
        }
        #[cfg(feature = "mips")]
        "mipsel" | "mips32le" | "mips32el" => {
            println!("Generating MIPS32 little-endian test specification...");
            build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            )
            .map_err(|e| e.to_string())?
        }
        "riscv64" | "rv64" | "rv64gc" => {
            println!("Generating RISC-V RV64 test specification...");
            create_riscv64_spec()
        }
        "riscv32" | "rv32" | "rv32gc" => {
            println!("Generating RISC-V RV32 test specification...");
            create_riscv32_spec()
        }
        _ => {
            return Err(format!(
                "Unknown architecture: {}. Supported: x86-64, arm, mips32be, mips32le, riscv64, riscv32",
                arch
            ));
        }
    };

    let output_path = match output {
        Some(p) => p.clone(),
        None => PathBuf::from(format!("{}.r2il", arch)),
    };

    validate_archspec(&spec).map_err(|e| format!("Invalid architecture specification: {}", e))?;

    serialize::save(&spec, &output_path).map_err(|e| e.to_string())?;

    println!("Output: {}", output_path.display());
    println!("  Architecture: {}", spec.name);
    println!("  Registers: {}", spec.registers.len());

    Ok(())
}

fn cmd_version() -> Result<(), String> {
    println!("r2sleigh {}", env!("CARGO_PKG_VERSION"));
    println!(
        "r2il format: {:?}",
        std::str::from_utf8(r2il::MAGIC).unwrap_or("invalid discriminator")
    );

    #[cfg(feature = "sleigh-config")]
    println!("Disasm support: enabled");
    #[cfg(not(feature = "sleigh-config"))]
    println!("Disasm support: disabled (build with --features x86, arm, or riscv to enable)");

    Ok(())
}

#[cfg(feature = "sleigh-config")]
fn parse_addr(addr_str: &str) -> Result<u64, String> {
    if addr_str.starts_with("0x") || addr_str.starts_with("0X") {
        u64::from_str_radix(&addr_str[2..], 16).map_err(|e| format!("Invalid address: {}", e))
    } else {
        addr_str
            .parse::<u64>()
            .map_err(|e| format!("Invalid address: {}", e))
    }
}

#[cfg(feature = "sleigh-config")]
fn parse_hex_bytes(bytes_hex: &str) -> Result<Vec<u8>, String> {
    let bytes = hex::decode(bytes_hex.replace(" ", "").replace("0x", ""))
        .map_err(|e| format!("Invalid hex bytes: {}", e))?;
    if bytes.is_empty() {
        return Err("No bytes provided".to_string());
    }
    Ok(bytes)
}

#[cfg(feature = "sleigh-config")]
fn make_instruction_input<'a>(
    disasm: &'a Disassembler,
    arch_spec: &'a r2il::ArchSpec,
    block: &'a r2il::R2ILBlock,
    addr: u64,
    mnemonic: &'a str,
    size: usize,
) -> InstructionExportInput<'a> {
    InstructionExportInput {
        disasm,
        arch: arch_spec,
        block,
        addr,
        mnemonic,
        native_size: size,
    }
}

#[cfg(feature = "sleigh-config")]
fn export_single_instruction(
    input: &InstructionExportInput<'_>,
    action: InstructionAction,
    format: ExportFormat,
) -> Result<String, String> {
    export_instruction(input, action, format).map_err(|e| e.to_string())
}

#[cfg(feature = "sleigh-config")]
fn build_disasm_json(
    disasm: &Disassembler,
    arch_spec: &r2il::ArchSpec,
    block: &r2il::R2ILBlock,
    mnemonic: &str,
    size: usize,
) -> Result<serde_json::Value, String> {
    let input = make_instruction_input(disasm, arch_spec, block, block.addr, mnemonic, size);
    let output = export_single_instruction(&input, InstructionAction::Lift, ExportFormat::Json)?;
    serde_json::from_str(&output).map_err(|e| format!("Failed to parse exporter JSON: {}", e))
}

#[cfg(feature = "sleigh-config")]
fn render_esil_lines(
    disasm: &Disassembler,
    arch_spec: &r2il::ArchSpec,
    bytes: &[u8],
    addr: u64,
) -> Result<Vec<String>, String> {
    const MIN_BYTES: usize = 16;
    let mut lines = Vec::new();
    let mut offset = 0usize;

    while offset < bytes.len() {
        let remaining = &bytes[offset..];
        if remaining.is_empty() {
            break;
        }

        let instr_addr = addr + offset as u64;
        let mut lift_bytes = remaining.to_vec();
        if lift_bytes.len() < MIN_BYTES {
            lift_bytes.resize(MIN_BYTES, 0);
        }

        let (mnemonic, _) = match disasm.disasm_native(&lift_bytes, instr_addr) {
            Ok(result) => result,
            Err(_) => break,
        };
        let block = match disasm.lift(&lift_bytes, instr_addr) {
            Ok(result) => result,
            Err(_) => break,
        };
        let instr_size = block.size as usize;
        if instr_size == 0 {
            break;
        }

        let input =
            make_instruction_input(disasm, arch_spec, &block, instr_addr, &mnemonic, instr_size);
        let exported =
            export_single_instruction(&input, InstructionAction::Lift, ExportFormat::Esil)?;
        lines.push(format!(
            "# 0x{:x}: {} (size={})",
            instr_addr, mnemonic, instr_size
        ));
        if !exported.is_empty() {
            lines.extend(exported.lines().map(ToString::to_string));
        }

        offset += instr_size;
    }

    Ok(lines)
}

#[cfg(feature = "sleigh-config")]
fn cmd_disasm(arch: &str, bytes_hex: &str, addr_str: &str, format: &str) -> Result<(), String> {
    let addr = parse_addr(addr_str)?;
    let bytes = parse_hex_bytes(bytes_hex)?;

    // Get the disassembler for the requested architecture
    let (disasm, arch_spec) = get_disassembler_with_spec(arch)?;

    // Lift the instruction
    let block = disasm
        .lift(&bytes, addr)
        .map_err(|e| format!("Lift failed: {}", e))?;

    // Also get the native disassembly for display
    let (mnemonic, size) = disasm
        .disasm_native(&bytes, addr)
        .map_err(|e| format!("Native disasm failed: {}", e))?;

    match format {
        "json" => {
            let json = build_disasm_json(&disasm, &arch_spec, &block, &mnemonic, size)?;
            let output = serde_json::to_string_pretty(&json)
                .map_err(|e| format!("Failed to render JSON: {}", e))?;
            println!("{}", output);
        }
        "esil" => {
            let lines = render_esil_lines(&disasm, &arch_spec, &bytes, addr)?;
            for line in lines {
                println!("{}", line);
            }
        }
        "r2cmd" => {
            let input = make_instruction_input(&disasm, &arch_spec, &block, addr, &mnemonic, size);
            let output =
                export_single_instruction(&input, InstructionAction::Lift, ExportFormat::R2Cmd)?;
            println!("{}", output);
        }
        _ => {
            let input = make_instruction_input(&disasm, &arch_spec, &block, addr, &mnemonic, size);
            let output =
                export_single_instruction(&input, InstructionAction::Lift, ExportFormat::Text)?;
            println!("{}", output);
        }
    }

    Ok(())
}

#[cfg(feature = "sleigh-config")]
fn cmd_run(
    arch: &str,
    bytes_hex: &str,
    addr_str: &str,
    action: InstructionAction,
    format: ExportFormat,
) -> Result<(), String> {
    let output = run_action_output(arch, bytes_hex, addr_str, action, format)?;
    println!("{}", output);
    Ok(())
}

#[cfg(feature = "sleigh-config")]
fn run_action_output(
    arch: &str,
    bytes_hex: &str,
    addr_str: &str,
    action: InstructionAction,
    format: ExportFormat,
) -> Result<String, String> {
    let addr = parse_addr(addr_str)?;
    let bytes = parse_hex_bytes(bytes_hex)?;
    let (disasm, arch_spec) = get_disassembler_with_spec(arch)?;
    let block = disasm
        .lift(&bytes, addr)
        .map_err(|e| format!("Lift failed: {}", e))?;
    let (mnemonic, size) = disasm
        .disasm_native(&bytes, addr)
        .map_err(|e| format!("Native disasm failed: {}", e))?;

    let input = make_instruction_input(&disasm, &arch_spec, &block, addr, &mnemonic, size);
    export_single_instruction(&input, action, format)
}

#[cfg(feature = "sleigh-config")]
#[allow(dead_code)]
fn get_disassembler(arch: &str) -> Result<Disassembler, String> {
    let (disasm, _) = get_disassembler_with_spec(arch)?;
    Ok(disasm)
}

#[cfg(feature = "sleigh-config")]
fn get_disassembler_with_spec(arch: &str) -> Result<(Disassembler, r2il::ArchSpec), String> {
    match arch.to_lowercase().as_str() {
        #[cfg(feature = "x86")]
        "x86-64" | "x86_64" | "x64" | "amd64" => {
            let spec = build_arch_spec(
                sleigh_config::processor_x86::SLA_X86_64,
                sleigh_config::processor_x86::PSPEC_X86_64,
                "x86-64",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_x86::SLA_X86_64,
                sleigh_config::processor_x86::PSPEC_X86_64,
                "x86-64",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("x86-64"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "x86")]
        "x86" | "x86-32" | "i386" | "i686" => {
            let spec = build_arch_spec(
                sleigh_config::processor_x86::SLA_X86,
                sleigh_config::processor_x86::PSPEC_X86,
                "x86",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_x86::SLA_X86,
                sleigh_config::processor_x86::PSPEC_X86,
                "x86",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("x86"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "arm")]
        "arm" | "arm32" | "arm-le" => {
            let spec = build_arch_spec(
                sleigh_config::processor_arm::SLA_ARM8_LE,
                sleigh_config::processor_arm::PSPEC_ARMCORTEX,
                "arm",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_arm::SLA_ARM8_LE,
                // sleigh-config 1.x does not ship an ARM8 pspec; use a Cortex pspec instead.
                sleigh_config::processor_arm::PSPEC_ARMCORTEX,
                "ARM",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("arm"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "arm")]
        "arm64" | "arm64e" | "aarch64" => {
            let mut spec = build_arch_spec(
                sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_aarch64::SLA_AARCH64_APPLESILICON,
                sleigh_config::processor_aarch64::PSPEC_AARCH64,
                "aarch64",
            )
            .map_err(|e| e.to_string())?;
            let userops = userop_map_for_arch("arm64");
            disasm.set_userop_map(userops.clone());
            spec.userops = userops
                .into_iter()
                .map(|(index, name)| r2il::serialize::UserOpDef { index, name })
                .collect();
            spec.userops.sort_by_key(|def| def.index);
            Ok((disasm, spec))
        }
        #[cfg(feature = "mips")]
        "mips" | "mips32" | "mips32be" | "mipsbe" | "mipseb" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS32BE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32be",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("mips32be"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "mips")]
        "mipsel" | "mips32le" | "mips32el" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS32LE,
                sleigh_config::processor_mips::PSPEC_MIPS32,
                "mips32le",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("mips32le"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "mips")]
        "mips64" | "mips64be" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS64BE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64be",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS64BE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64be",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("mips64be"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "mips")]
        "mips64el" | "mips64le" => {
            let spec = build_arch_spec(
                sleigh_config::processor_mips::SLA_MIPS64LE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64le",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_mips::SLA_MIPS64LE,
                sleigh_config::processor_mips::PSPEC_MIPS64,
                "mips64le",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("mips64le"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "riscv")]
        "riscv64" | "rv64" | "rv64gc" => {
            let spec = build_arch_spec(
                sleigh_config::processor_riscv::SLA_RISCV_LP64D,
                sleigh_config::processor_riscv::PSPEC_RV64GC,
                "riscv64",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_riscv::SLA_RISCV_LP64D,
                sleigh_config::processor_riscv::PSPEC_RV64GC,
                "riscv64",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("riscv64"));
            Ok((disasm, spec))
        }
        #[cfg(feature = "riscv")]
        "riscv32" | "rv32" | "rv32gc" => {
            let spec = build_arch_spec(
                sleigh_config::processor_riscv::SLA_RISCV_ILP32D,
                sleigh_config::processor_riscv::PSPEC_RV32GC,
                "riscv32",
            )
            .map_err(|e| e.to_string())?;
            let mut disasm = Disassembler::from_sla(
                sleigh_config::processor_riscv::SLA_RISCV_ILP32D,
                sleigh_config::processor_riscv::PSPEC_RV32GC,
                "riscv32",
            )
            .map_err(|e| e.to_string())?;
            disasm.set_userop_map(userop_map_for_arch("riscv32"));
            Ok((disasm, spec))
        }
        _ => {
            let mut supported: Vec<&str> = vec![];
            #[cfg(feature = "x86")]
            supported.extend(["x86-64", "x86"]);
            #[cfg(feature = "arm")]
            supported.extend(["arm", "arm64", "aarch64"]);
            #[cfg(feature = "mips")]
            supported.extend(["mips32be", "mips32le", "mips64be", "mips64le"]);
            #[cfg(feature = "riscv")]
            supported.extend(["riscv64", "riscv32"]);

            if supported.is_empty() {
                Err(
                    "No architectures enabled. Build with --features x86, arm, mips, or riscv"
                        .to_string(),
                )
            } else {
                Err(format!(
                    "Unknown architecture '{}'. Supported: {}",
                    arch,
                    supported.join(", ")
                ))
            }
        }
    }
}

#[cfg(all(test, feature = "sleigh-config", feature = "x86"))]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    const X86_BYTES_MINIMAL: &str = "4889c000000000000000000000000000";
    const X86_BYTES_DEC: &str = "48ffc000000000000000000000000000";
    #[cfg(feature = "arm")]
    const ARM_BYTES: &str = "0100a0e3000000000000000000000000";
    #[cfg(feature = "arm")]
    const ARM64_PACIBSP_BYTES: &str = "7f2303d5000000000000000000000000";
    #[cfg(feature = "riscv")]
    const RISCV_BYTES: &str = "13051500000000000000000000000000";

    fn canonicalize_json(value: &serde_json::Value) -> serde_json::Value {
        match value {
            serde_json::Value::Object(map) => {
                let mut sorted = BTreeMap::new();
                for (k, v) in map {
                    sorted.insert(k.clone(), canonicalize_json(v));
                }
                let mut out = serde_json::Map::new();
                for (k, v) in sorted {
                    out.insert(k, v);
                }
                serde_json::Value::Object(out)
            }
            serde_json::Value::Array(items) => {
                serde_json::Value::Array(items.iter().map(canonicalize_json).collect())
            }
            _ => value.clone(),
        }
    }

    fn normalize_text_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let mut lines: Vec<String> = text.lines().map(|l| l.trim_end().to_string()).collect();
        while lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        lines.join("\n")
    }

    fn normalize_json_output(output: &str) -> String {
        let parsed: serde_json::Value = serde_json::from_str(output.trim()).expect("valid json");
        canonicalize_json(&parsed).to_string()
    }

    #[cfg(feature = "decompile")]
    fn normalize_c_like_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let mut lines = Vec::new();
        let mut prev_blank = false;
        for raw_line in text.lines() {
            let line = raw_line.trim_end();
            let is_blank = line.is_empty();
            if is_blank && prev_blank {
                continue;
            }
            lines.push(line.to_string());
            prev_blank = is_blank;
        }
        while lines.first().is_some_and(|l| l.is_empty()) {
            lines.remove(0);
        }
        while lines.last().is_some_and(|l| l.is_empty()) {
            lines.pop();
        }
        lines.join("\n")
    }

    fn normalize_r2cmd_output(output: &str) -> String {
        let text = output.replace("\r\n", "\n");
        let lines: Vec<&str> = text.lines().collect();
        assert!(!lines.is_empty(), "r2cmd output must not be empty");
        assert_eq!(lines.len() % 2, 0, "r2cmd output must be line-paired");
        let mut normalized = Vec::new();
        for (idx, line) in lines.iter().enumerate() {
            let line = line.trim_end();
            if idx % 2 == 0 {
                assert!(
                    line.starts_with("# "),
                    "expected sidecar comment line at index {}",
                    idx
                );
                let sidecar: serde_json::Value =
                    serde_json::from_str(line.trim_start_matches("# ")).expect("sidecar json");
                normalized.push(format!("# {}", canonicalize_json(&sidecar)));
            } else {
                assert!(
                    line.starts_with("ae "),
                    "expected ae replay line at index {}",
                    idx
                );
                normalized.push(line.to_string());
            }
        }
        normalized.join("\n")
    }

    fn assert_deterministic_output(
        arch: &str,
        bytes_hex: &str,
        action: InstructionAction,
        format: ExportFormat,
        normalizer: fn(&str) -> String,
    ) -> String {
        let run1 = run_action_output(arch, bytes_hex, "0x1000", action, format)
            .expect("first run output should succeed");
        let run2 = run_action_output(arch, bytes_hex, "0x1000", action, format)
            .expect("second run output should succeed");
        let norm1 = normalizer(&run1);
        let norm2 = normalizer(&run2);
        assert_eq!(
            norm1, norm2,
            "non-deterministic output for arch={}, action={}, format={}",
            arch, action, format
        );
        norm1
    }

    fn assert_json_shape_for_action(action: InstructionAction, normalized_json: &str) {
        let parsed: serde_json::Value = serde_json::from_str(normalized_json).expect("valid json");
        match action {
            InstructionAction::Lift => {
                assert!(
                    parsed
                        .get("ops")
                        .and_then(serde_json::Value::as_array)
                        .is_some_and(|ops| !ops.is_empty()),
                    "lift json must contain non-empty ops"
                );
                assert!(
                    parsed.get("mnemonic").is_some(),
                    "lift json must have mnemonic"
                );
                assert!(parsed.get("size").is_some(), "lift json must have size");
            }
            InstructionAction::Ssa => {
                assert!(
                    parsed.as_array().is_some_and(|ops| !ops.is_empty()),
                    "ssa json must contain non-empty array"
                );
            }
            InstructionAction::Defuse => {
                assert!(
                    parsed.get("inputs").is_some(),
                    "defuse json must have inputs"
                );
                assert!(
                    parsed.get("outputs").is_some(),
                    "defuse json must have outputs"
                );
                assert!(parsed.get("live").is_some(), "defuse json must have live");
            }
            InstructionAction::Dec => {
                assert!(
                    parsed.as_array().is_some(),
                    "dec json must be a statement array"
                );
            }
        }
    }

    fn run_matrix_for_arch(arch: &str, bytes_hex: &str, dec_bytes_hex: &str) {
        #[cfg(not(feature = "decompile"))]
        let _ = dec_bytes_hex;

        for format in [
            ExportFormat::Json,
            ExportFormat::Text,
            ExportFormat::Esil,
            ExportFormat::R2Cmd,
        ] {
            let normalized = assert_deterministic_output(
                arch,
                bytes_hex,
                InstructionAction::Lift,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text | ExportFormat::Esil => normalize_text_output,
                    ExportFormat::R2Cmd => normalize_r2cmd_output,
                    ExportFormat::CLike => unreachable!("not part of lift matrix"),
                },
            );
            match format {
                ExportFormat::Json => {
                    assert_json_shape_for_action(InstructionAction::Lift, &normalized)
                }
                ExportFormat::Text | ExportFormat::Esil | ExportFormat::R2Cmd => {
                    assert!(
                        !normalized.trim().is_empty(),
                        "lift output must be non-empty"
                    )
                }
                ExportFormat::CLike => unreachable!("not part of lift matrix"),
            }
        }

        for format in [ExportFormat::Json, ExportFormat::Text] {
            let normalized = assert_deterministic_output(
                arch,
                bytes_hex,
                InstructionAction::Ssa,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text => normalize_text_output,
                    _ => unreachable!("ssa supports json/text"),
                },
            );
            match format {
                ExportFormat::Json => {
                    assert_json_shape_for_action(InstructionAction::Ssa, &normalized)
                }
                ExportFormat::Text => {
                    assert!(!normalized.trim().is_empty(), "ssa text must be non-empty")
                }
                _ => unreachable!("ssa supports json/text"),
            }
        }

        for format in [ExportFormat::Json, ExportFormat::Text] {
            let normalized = assert_deterministic_output(
                arch,
                bytes_hex,
                InstructionAction::Defuse,
                format,
                match format {
                    ExportFormat::Json => normalize_json_output,
                    ExportFormat::Text => normalize_text_output,
                    _ => unreachable!("defuse supports json/text"),
                },
            );
            match format {
                ExportFormat::Json => {
                    assert_json_shape_for_action(InstructionAction::Defuse, &normalized)
                }
                ExportFormat::Text => {
                    assert!(
                        !normalized.trim().is_empty(),
                        "defuse text must be non-empty"
                    )
                }
                _ => unreachable!("defuse supports json/text"),
            }
        }

        #[cfg(feature = "decompile")]
        {
            for format in [ExportFormat::CLike, ExportFormat::Json, ExportFormat::Text] {
                let normalized = assert_deterministic_output(
                    arch,
                    dec_bytes_hex,
                    InstructionAction::Dec,
                    format,
                    match format {
                        ExportFormat::CLike => normalize_c_like_output,
                        ExportFormat::Json => normalize_json_output,
                        ExportFormat::Text => normalize_text_output,
                        _ => unreachable!("dec supports c_like/json/text"),
                    },
                );
                match format {
                    ExportFormat::Json => {
                        assert_json_shape_for_action(InstructionAction::Dec, &normalized)
                    }
                    ExportFormat::CLike | ExportFormat::Text => {
                        assert!(
                            !normalized.trim().is_empty(),
                            "dec output must be non-empty"
                        )
                    }
                    _ => unreachable!("dec supports c_like/json/text"),
                }
            }
        }
    }

    fn contains_named_register(value: &serde_json::Value) -> bool {
        match value {
            serde_json::Value::Object(map) => {
                let is_varnode = map.contains_key("space")
                    && map.contains_key("offset")
                    && map.contains_key("size");
                if is_varnode {
                    let space = map.get("space").and_then(serde_json::Value::as_str);
                    if let Some(space_str) = space
                        && space_str.eq_ignore_ascii_case("register")
                        && let Some(name) = map.get("name").and_then(serde_json::Value::as_str)
                        && !name.is_empty()
                    {
                        return true;
                    }
                }

                map.values().any(contains_named_register)
            }
            serde_json::Value::Array(items) => items.iter().any(contains_named_register),
            _ => false,
        }
    }

    #[test]
    fn disasm_json_includes_named_registers() {
        let (disasm, arch_spec) = get_disassembler_with_spec("x86-64").expect("disassembler");
        let bytes = hex::decode("4889e500000000000000000000000000").expect("bytes");
        let block = disasm.lift(&bytes, 0x1000).expect("lift");
        let (mnemonic, size) = disasm.disasm_native(&bytes, 0x1000).expect("disasm");
        let json = build_disasm_json(&disasm, &arch_spec, &block, &mnemonic, size).expect("json");
        let ops = json
            .get("ops")
            .and_then(serde_json::Value::as_array)
            .expect("ops array");
        assert!(!ops.is_empty(), "CLI JSON should include ops");
        assert!(ops[0].is_object(), "CLI JSON ops should be objects");
        assert!(
            contains_named_register(&json),
            "CLI JSON should include named register varnodes"
        );
    }

    #[test]
    fn disasm_esil_includes_userop_name_across_instructions() {
        let (disasm, arch_spec) = get_disassembler_with_spec("x86-64").expect("disassembler");
        let bytes = hex::decode("31c00fa2c3ffffffffffffffffffffffff").expect("bytes");
        let lines = render_esil_lines(&disasm, &arch_spec, &bytes, 0x1000).expect("render esil");
        assert!(
            lines
                .iter()
                .any(|line| line.contains("CALLOTHER(") && line.contains("cpuid")),
            "ESIL should include named CallOther ops across multiple instructions"
        );
    }

    #[test]
    fn exporter_path_reports_semantic_failure() {
        let arch = r2il::ArchSpec::new("test");
        let mut block = r2il::R2ILBlock::new(0x1000, 1);
        block.push(r2il::R2ILOp::Copy {
            dst: r2il::Varnode::register(0, 8),
            src: r2il::Varnode::register(8, 4),
        });

        let (disasm, _) = get_disassembler_with_spec("x86-64").expect("disassembler");
        let input = make_instruction_input(&disasm, &arch, &block, 0x1000, "copy", 1);
        let err = export_single_instruction(&input, InstructionAction::Lift, ExportFormat::Json)
            .expect_err("must fail");
        assert!(
            err.contains("validation failed") && err.contains("op.copy.width_mismatch"),
            "expected semantic validation failure, got: {}",
            err
        );
    }

    #[test]
    fn disasm_json_includes_op_metadata_when_present() {
        let (disasm, arch_spec) = get_disassembler_with_spec("x86-64").expect("disassembler");
        let mut block = r2il::R2ILBlock::new(0x1000, 1);
        block.push_with_metadata(
            r2il::R2ILOp::Copy {
                dst: r2il::Varnode::register(0, 8),
                src: r2il::Varnode::constant(1, 8),
            },
            Some(r2il::OpMetadata {
                instruction_addr: None,
                memory_class: Some(r2il::MemoryClass::Stack),
                endianness: None,
                memory_ordering: None,
                permissions: None,
                valid_range: None,
                bank_id: None,
                segment_id: None,
                atomic_kind: None,
            }),
        );

        let json = build_disasm_json(&disasm, &arch_spec, &block, "mov", 1).expect("json");
        let op_meta = json
            .get("op_metadata")
            .and_then(serde_json::Value::as_object)
            .expect("op_metadata object");
        let idx0 = op_meta
            .get("0")
            .and_then(serde_json::Value::as_object)
            .expect("index 0 metadata");
        assert_eq!(
            idx0.get("memory_class").and_then(serde_json::Value::as_str),
            Some("stack")
        );
    }

    #[test]
    fn conformance_matrix_x86_64_deterministic() {
        run_matrix_for_arch("x86-64", X86_BYTES_MINIMAL, X86_BYTES_DEC);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn conformance_matrix_arm_deterministic() {
        run_matrix_for_arch("arm", ARM_BYTES, ARM_BYTES);
    }

    #[test]
    #[cfg(feature = "arm")]
    fn arm64_alias_lifts_pointer_auth_userop() {
        let out = run_action_output(
            "arm64",
            ARM64_PACIBSP_BYTES,
            "0x1000",
            InstructionAction::Lift,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert_eq!(
            parsed["ops"][0]["CallOther"]["userop"].as_u64(),
            Some(0xffff_0002)
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn conformance_matrix_riscv64_deterministic() {
        run_matrix_for_arch("riscv64", RISCV_BYTES, RISCV_BYTES);
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn conformance_matrix_riscv32_deterministic() {
        run_matrix_for_arch("riscv32", RISCV_BYTES, RISCV_BYTES);
    }

    #[test]
    fn run_lift_json_success() {
        let out = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Lift,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert!(
            parsed
                .get("ops")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|ops| !ops.is_empty()),
            "lift json must contain ops"
        );
    }

    #[test]
    fn run_lift_r2cmd_success() {
        let out = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Lift,
            ExportFormat::R2Cmd,
        )
        .expect("run output");
        let lines: Vec<&str> = out.lines().collect();
        assert!(
            lines.first().is_some_and(|l| l.starts_with("# ")),
            "r2cmd must start with sidecar line"
        );
        assert!(
            lines.get(1).is_some_and(|l| l.starts_with("ae ")),
            "r2cmd must include ae replay line"
        );
    }

    #[test]
    fn storeconditional_esil_uses_zero_success_code() {
        let (disasm, _) = get_disassembler_with_spec("x86-64").expect("disassembler");
        let op = r2il::R2ILOp::StoreConditional {
            result: Some(r2il::Varnode::new(r2il::SpaceId::Unique, 0x10, 1)),
            space: r2il::SpaceId::Ram,
            addr: r2il::Varnode::new(r2il::SpaceId::Unique, 0x20, 8),
            val: r2il::Varnode::new(r2il::SpaceId::Unique, 0x30, 8),
            ordering: r2il::MemoryOrdering::Relaxed,
        };
        let esil = r2sleigh_lift::op_to_esil(&disasm, &op);
        assert_eq!(esil, "tmp:0x30,tmp:0x20,=[8],0,tmp:0x10,=");
    }

    #[test]
    fn run_ssa_text_success() {
        let out = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Ssa,
            ExportFormat::Text,
        )
        .expect("run output");
        assert!(
            out.contains("dst="),
            "ssa text output should contain destination annotations"
        );
    }

    #[test]
    fn run_defuse_json_success() {
        let out = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Defuse,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert!(
            parsed.get("inputs").is_some(),
            "defuse JSON should include inputs"
        );
        assert!(
            parsed.get("outputs").is_some(),
            "defuse JSON should include outputs"
        );
        assert!(
            parsed.get("live").is_some(),
            "defuse JSON should include live"
        );
    }

    #[test]
    #[cfg(feature = "decompile")]
    fn run_dec_c_like_success() {
        let out = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Dec,
            ExportFormat::CLike,
        )
        .expect("run output");
        assert!(!out.trim().is_empty(), "c_like output should be non-empty");
    }

    #[test]
    fn run_invalid_combo_errors_cleanly() {
        let err = run_action_output(
            "x86-64",
            "31c00000000000000000000000000000",
            "0x1000",
            InstructionAction::Ssa,
            ExportFormat::Esil,
        )
        .expect_err("unsupported combo should fail");
        assert!(
            err.contains("unsupported action/format combination")
                && err.contains("action=ssa")
                && err.contains("format=esil"),
            "unexpected error: {}",
            err
        );
    }

    #[test]
    fn info_lines_include_instruction_and_memory_endianness() {
        let mut spec = r2il::ArchSpec::new("test");
        spec.set_instruction_endianness(r2il::Endianness::Big);
        spec.set_memory_endianness(r2il::Endianness::Little);
        let (instruction, memory) = endianness_info_lines(&spec);
        assert!(instruction.contains("Instruction endianness: Big"));
        assert!(memory.contains("Memory endianness: Little"));
    }

    #[test]
    fn extracted_spec_sets_exact_endianness_and_space_overrides() {
        let (_, spec) = get_disassembler_with_spec("x86-64").expect("disassembler");
        assert_eq!(spec.instruction_endianness, r2il::Endianness::Little);
        assert_eq!(spec.memory_endianness, r2il::Endianness::Little);
        assert!(
            spec.spaces.iter().any(|space| space.endianness.is_some()),
            "extracted spaces should carry explicit endianness overrides"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn disasm_riscv64_json_success() {
        let out = run_action_output(
            "riscv64",
            "13050500000000000000000000000000",
            "0x1000",
            InstructionAction::Lift,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert!(
            parsed
                .get("ops")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|ops| !ops.is_empty()),
            "riscv64 lift json must contain ops"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn run_riscv64_lift_json_success() {
        let out = run_action_output(
            "riscv64",
            "13050500000000000000000000000000",
            "0x1000",
            InstructionAction::Lift,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert!(
            parsed
                .get("ops")
                .and_then(serde_json::Value::as_array)
                .is_some_and(|ops| !ops.is_empty()),
            "riscv64 lift json must contain ops"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn run_riscv64_ssa_text_success() {
        let out = run_action_output(
            "riscv64",
            "13050500000000000000000000000000",
            "0x1000",
            InstructionAction::Ssa,
            ExportFormat::Text,
        )
        .expect("run output");
        assert!(
            out.contains("dst="),
            "riscv64 ssa text output should contain destination annotations"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn run_riscv64_defuse_json_success() {
        let out = run_action_output(
            "riscv64",
            "13050500000000000000000000000000",
            "0x1000",
            InstructionAction::Defuse,
            ExportFormat::Json,
        )
        .expect("run output");
        let parsed: serde_json::Value = serde_json::from_str(&out).expect("json");
        assert!(parsed.get("inputs").is_some(), "defuse must include inputs");
        assert!(
            parsed.get("outputs").is_some(),
            "defuse must include outputs"
        );
        assert!(parsed.get("live").is_some(), "defuse must include live");
    }

    #[test]
    #[cfg(all(feature = "riscv", feature = "decompile"))]
    fn run_riscv64_dec_c_like_success() {
        let out = run_action_output(
            "riscv64",
            "13050500000000000000000000000000",
            "0x1000",
            InstructionAction::Dec,
            ExportFormat::CLike,
        )
        .expect("run output");
        assert!(
            !out.contains("unsupported action/format combination"),
            "riscv64 c_like path should be reachable"
        );
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn test_arch_riscv64_generates_valid_spec() {
        let spec = create_riscv64_spec();
        validate_archspec(&spec).expect("riscv64 spec should validate");
        assert_eq!(spec.addr_size, 8);
    }

    #[test]
    #[cfg(feature = "riscv")]
    fn test_arch_riscv32_generates_valid_spec() {
        let spec = create_riscv32_spec();
        validate_archspec(&spec).expect("riscv32 spec should validate");
        assert_eq!(spec.addr_size, 4);
    }
}

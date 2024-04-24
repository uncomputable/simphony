use std::env;
use std::str::FromStr;
use std::sync::Arc;

use base64::display::Base64Display;
use base64::engine::general_purpose::STANDARD;

use simfony::named::NamedExt;
use simfony::{Compiler, Witness};

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    // Get the command-line arguments as a Vec<String>.
    let args: Vec<String> = env::args().collect();

    // Check if at least two arguments are provided.
    if args.len() < 2 {
        println!("Usage: {} <prog.simf> [sig.wit]", args[0]);
        println!("If no witness file is provided, the program will be compiled and printed.");
        println!("If a witness file is provided, the program will be satisfied and printed.");
        return Ok(());
    }

    // Extract the first argument (arg1).
    let program_path = std::path::Path::new(&args[1]);
    let program_str = std::fs::read_to_string(program_path)
        .map(Arc::<str>::from)
        .map_err(|e| format!("Cannot open program: {e}"))?;

    // Check if a second argument (arg2) is provided.
    if args.len() >= 3 {
        let witness_path = std::path::Path::new(&args[2]);
        let witness_str = std::fs::read_to_string(witness_path)
            .map_err(|e| format!("Cannot open witness: {e}"))?;
        let witness =
            Witness::from_str(&witness_str).map_err(|e| format!("Cannot parse witness: {e}"))?;

        let redeem = Compiler::new()
            .with_program(program_str)
            .with_witness(witness)
            .get_redeem()?;
        let redeem_bytes = redeem.encode_to_vec();
        println!("{}", Base64Display::new(&redeem_bytes, &STANDARD));
    } else {
        let named_commit = Compiler::new()
            .with_program(program_str)
            .get_named_commit()?;
        let commit_bytes = named_commit.to_commit_node().encode_to_vec();
        println!("{}", Base64Display::new(&commit_bytes, &STANDARD));
    }

    Ok(())
}

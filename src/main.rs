//! `dt` — find a Lean declaration by shape, and lift it into a proof.

use discrtree::interface::cli::Cli;
use discrtree::interface::run;

fn main() {
    let cli = Cli::read(std::env::args_os().collect()).unwrap_or_else(|e| e.exit());
    if let Err(e) = run::run(cli) {
        eprintln!("dt: {e}");
        std::process::exit(1);
    }
}

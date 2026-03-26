#![forbid(unsafe_code)]

use std::env;

use anyhow::{Result, bail};

mod toolchain;
mod unit_test;

fn main() -> Result<()> {
    let mut args = env::args().skip(1);

    match args.next().as_deref() {
        None | Some("help") => print_help(),
        Some("test-unit") => unit_test::run(args)?,
        Some(command @ ("list" | "init" | "fetch" | "build" | "clean")) => {
            let forwarded = std::iter::once(command.to_owned()).chain(args);
            toolchain::run(forwarded)?;
        }
        Some(other) => bail!("unsupported command: {other}"),
    }

    Ok(())
}

fn print_help() {
    println!("usage:");
    println!("  cargo lua help");
    println!("  cargo lua list");
    println!("  cargo lua init [all|toolchain]");
    println!("  cargo lua fetch <all|toolchain>");
    println!("  cargo lua build <all|toolchain>");
    println!("  cargo lua clean <all|toolchain>");
    unit_test::print_help();
}

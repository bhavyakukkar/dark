use std::{env, fs};

fn main() {
    match run() {
        Ok(msg) => {
            println!("{}", msg);
            std::process::exit(0);
        }
        Err(err) => {
            eprintln!("{}", err);
            std::process::exit(1);
        }
    }
}

fn run() -> Result<String, String> {
    #[rustfmt::skip]
    let help = format!(
"Usage: {} <subcommand>
  subcommands:
    lex <file>\t\tProduce lexical analysis of file
    help\t\tPrint this help",
        env::args().nth(0).unwrap_or("dark".to_owned())
    );

    let subcommand = env::args()
        .nth(1)
        .ok_or_else(|| help.clone() + "\nSubcommand not provided")?;

    match subcommand.as_str() {
        "lex" | "Lex" | "LEX" => {
            let file_name = env::args()
                .nth(2)
                .ok_or_else(|| help.clone() + "\nLex file not provided")?;

            let file_contents = fs::read_to_string(file_name)
                .map_err(|err| format!("Error reading file: {}", err))?;

            let program =
                dark::lex(file_contents).map_err(|err| format!("Error parsing file: {}", err))?;

            Ok(program
                .iter()
                .map(|token| token.to_string() + "\n")
                .fold(String::new(), |a, b| a + &b))
        }
        "help" | "Help" | "HELP" => Ok(help),
        _ => Err(help + "\nUnrecognized subcommand"),
    }
}

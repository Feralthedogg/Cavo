pub mod ast;
pub mod lexer;
pub mod parser;
pub mod token;

/// Source compatibility baseline. Optional extensions are outside this grammar.
pub const GRAMMAR_VERSION: &str = "cavo-0.1";
pub const GRAMMAR: &str = include_str!("../../grammar/cavo-0.1.ebnf");

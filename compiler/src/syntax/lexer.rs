use super::token::{Keyword, Token, TokenKind};
use crate::{
    diagnostic::Diagnostic,
    source::{SourceFile, Span},
    symbol::Interner,
};

pub fn lex(
    source: &SourceFile,
    symbols: &mut Interner,
    diagnostics: &mut Vec<Diagnostic>,
) -> Vec<Token> {
    Lexer {
        source,
        symbols,
        diagnostics,
        offset: 0,
    }
    .run()
}

struct Lexer<'a> {
    source: &'a SourceFile,
    symbols: &'a mut Interner,
    diagnostics: &'a mut Vec<Diagnostic>,
    offset: usize,
}

impl Lexer<'_> {
    fn run(mut self) -> Vec<Token> {
        let mut tokens = Vec::new();
        while self.offset < self.source.text().len() {
            self.trivia();
            if self.offset == self.source.text().len() {
                break;
            }
            let start = self.offset;
            let byte = self.bytes()[self.offset];
            let kind = if byte.is_ascii_alphabetic() || byte == b'_' {
                self.offset += 1;
                while self.peek().is_some_and(is_ident_continue) {
                    self.offset += 1;
                }
                let word = &self.source.text()[start..self.offset];
                if word == "_" {
                    TokenKind::Underscore
                } else {
                    Keyword::from_text(word).map_or_else(
                        || TokenKind::Ident(self.symbols.intern(word)),
                        TokenKind::Keyword,
                    )
                }
            } else if byte.is_ascii_digit() {
                self.number(start)
            } else if byte == b'"' {
                self.quoted(start, b'"');
                TokenKind::String
            } else if byte == b'\'' {
                self.apostrophe(start)
            } else if let Some((length, kind)) = self.punctuation() {
                self.offset += length;
                kind
            } else {
                let ch = self.source.text()[self.offset..]
                    .chars()
                    .next()
                    .expect("nonempty source tail");
                self.offset += ch.len_utf8();
                self.error(
                    "E-LEX-001",
                    format!("unexpected character {ch:?}; identifiers use ASCII"),
                    start,
                );
                continue;
            };
            tokens.push(Token {
                kind,
                span: self.span(start),
            });
        }
        let end = self.offset as u32;
        tokens.push(Token {
            kind: TokenKind::Eof,
            span: Span::new(self.source.id, end, end),
        });
        tokens
    }

    fn bytes(&self) -> &[u8] {
        self.source.text().as_bytes()
    }
    fn peek(&self) -> Option<u8> {
        self.bytes().get(self.offset).copied()
    }
    fn span(&self, start: usize) -> Span {
        Span::new(self.source.id, start as u32, self.offset as u32)
    }

    fn error(&mut self, code: &'static str, message: impl Into<String>, start: usize) {
        crate::diagnostic::report(
            self.diagnostics,
            Diagnostic::error(code, message, self.span(start)),
        );
    }

    fn trivia(&mut self) {
        loop {
            while self.peek().is_some_and(|b| b.is_ascii_whitespace()) {
                self.offset += 1;
            }
            let tail = &self.bytes()[self.offset..];
            if tail.starts_with(b"//") {
                while self.peek().is_some_and(|b| b != b'\n') {
                    self.offset += 1;
                }
            } else if tail.starts_with(b"/*") {
                let start = self.offset;
                self.offset += 2;
                let mut depth = 1_usize;
                while self.offset < self.bytes().len() && depth > 0 {
                    let tail = &self.bytes()[self.offset..];
                    if tail.starts_with(b"/*") {
                        depth += 1;
                        self.offset += 2;
                    } else if tail.starts_with(b"*/") {
                        depth -= 1;
                        self.offset += 2;
                    } else {
                        self.offset += 1;
                    }
                }
                if depth != 0 {
                    self.error("E-LEX-002", "unterminated block comment", start);
                }
            } else {
                break;
            }
        }
    }

    fn number(&mut self, start: usize) -> TokenKind {
        let mut radix = 10;
        if self.bytes()[start..].starts_with(b"0x") || self.bytes()[start..].starts_with(b"0X") {
            radix = 16;
            self.offset += 2;
        } else if self.bytes()[start..].starts_with(b"0b")
            || self.bytes()[start..].starts_with(b"0B")
        {
            radix = 2;
            self.offset += 2;
        } else if self.bytes()[start..].starts_with(b"0o")
            || self.bytes()[start..].starts_with(b"0O")
        {
            radix = 8;
            self.offset += 2;
        }
        let digits = self.offset;
        while self
            .peek()
            .is_some_and(|b| b == b'_' || (b as char).is_digit(radix))
        {
            self.offset += 1;
        }
        if self.offset == digits || self.bytes()[digits..self.offset].iter().all(|&b| b == b'_') {
            self.error("E-LEX-004", "numeric literal requires digits", start);
        }
        let mut float = false;
        if radix == 10 {
            if self.peek() == Some(b'.')
                && self
                    .bytes()
                    .get(self.offset + 1)
                    .is_some_and(u8::is_ascii_digit)
            {
                float = true;
                self.offset += 1;
                while self.peek().is_some_and(|b| b.is_ascii_digit() || b == b'_') {
                    self.offset += 1;
                }
            }
            if matches!(self.peek(), Some(b'e' | b'E')) {
                float = true;
                self.offset += 1;
                if matches!(self.peek(), Some(b'+' | b'-')) {
                    self.offset += 1;
                }
                let exponent = self.offset;
                while self.peek().is_some_and(|b| b.is_ascii_digit() || b == b'_') {
                    self.offset += 1;
                }
                if exponent == self.offset
                    || self.bytes()[exponent..self.offset]
                        .iter()
                        .all(|&b| b == b'_')
                {
                    self.error("E-LEX-004", "exponent requires digits", start);
                }
            }
        }
        let suffix = self.offset;
        while self.peek().is_some_and(is_ident_continue) {
            self.offset += 1;
        }
        let suffix = &self.source.text()[suffix..self.offset];
        if suffix == "f32" || suffix == "f64" {
            float = true;
        }
        if radix != 10 && suffix.starts_with(|c: char| c.is_ascii_digit()) {
            self.error("E-LEX-004", "digit is invalid for this radix", start);
        }
        if float {
            TokenKind::Float
        } else {
            TokenKind::Integer
        }
    }

    fn apostrophe(&mut self, start: usize) -> TokenKind {
        self.offset += 1;
        if self
            .peek()
            .is_some_and(|b| b.is_ascii_alphabetic() || b == b'_')
        {
            let name = self.offset;
            while self.peek().is_some_and(is_ident_continue) {
                self.offset += 1;
            }
            if self.peek() != Some(b'\'') {
                return TokenKind::Lifetime(
                    self.symbols.intern(&self.source.text()[name..self.offset]),
                );
            }
        }
        self.offset = start;
        self.quoted(start, b'\'');
        TokenKind::Char
    }

    fn quoted(&mut self, start: usize, delimiter: u8) {
        self.offset += 1;
        let mut scalars = 0;
        while let Some(byte) = self.peek() {
            if byte == delimiter {
                self.offset += 1;
                if delimiter == b'\'' && scalars != 1 {
                    self.error(
                        "E-LEX-003",
                        "character literal must contain one Unicode scalar",
                        start,
                    );
                }
                return;
            }
            if matches!(byte, b'\n' | b'\r') {
                break;
            }
            scalars += 1;
            if byte == b'\\' {
                self.offset += 1;
                match self.peek() {
                    Some(b'n' | b'r' | b't' | b'0' | b'\\' | b'\'' | b'"') => self.offset += 1,
                    Some(b'x') => {
                        self.offset += 1;
                        let mut value = 0;
                        for _ in 0..2 {
                            if let Some(digit) = self.peek().and_then(|b| (b as char).to_digit(16))
                            {
                                value = value * 16 + digit;
                                self.offset += 1;
                            } else {
                                self.error(
                                    "E-LEX-003",
                                    "expected two hexadecimal escape digits",
                                    start,
                                );
                                break;
                            }
                        }
                        if value > 0x7f {
                            self.error(
                                "E-LEX-003",
                                "hex escapes must be ASCII; use a Unicode escape",
                                start,
                            );
                        }
                    }
                    Some(b'u') => {
                        self.offset += 1;
                        if self.peek() != Some(b'{') {
                            self.error("E-LEX-003", "expected '{' after Unicode escape", start);
                            continue;
                        }
                        self.offset += 1;
                        let digits = self.offset;
                        let mut value = Some(0_u32);
                        while let Some(digit) = self.peek().and_then(|b| (b as char).to_digit(16)) {
                            value = value.and_then(|n| n.checked_mul(16)?.checked_add(digit));
                            self.offset += 1;
                        }
                        if self.peek() == Some(b'}') {
                            self.offset += 1;
                        } else {
                            self.error("E-LEX-003", "unterminated Unicode escape", start);
                        }
                        if digits == self.offset - 1 || value.and_then(char::from_u32).is_none() {
                            self.error("E-LEX-003", "invalid Unicode scalar escape", start);
                        }
                    }
                    Some(_) => {
                        self.offset += self.source.text()[self.offset..]
                            .chars()
                            .next()
                            .expect("escape tail")
                            .len_utf8();
                        self.error("E-LEX-003", "unknown escape sequence", start);
                    }
                    None => break,
                }
            } else {
                let ch = self.source.text()[self.offset..]
                    .chars()
                    .next()
                    .expect("nonempty literal tail");
                self.offset += ch.len_utf8();
            }
        }
        self.error("E-LEX-003", "unterminated literal", start);
    }

    fn punctuation(&self) -> Option<(usize, TokenKind)> {
        use TokenKind::*;
        let tail = &self.bytes()[self.offset..];
        for (text, kind) in [
            ("<<=", ShiftLeftEqual),
            (">>=", ShiftRightEqual),
            ("...", Ellipsis),
            ("::", ColonColon),
            ("..", DotDot),
            ("->", Arrow),
            ("=>", FatArrow),
            ("<=", LessEqual),
            (">=", GreaterEqual),
            ("==", EqualEqual),
            ("!=", BangEqual),
            ("&&", AmpAmp),
            ("||", PipePipe),
            ("<<", ShiftLeft),
            (">>", ShiftRight),
            ("+=", PlusEqual),
            ("-=", MinusEqual),
            ("*=", StarEqual),
            ("/=", SlashEqual),
            ("%=", PercentEqual),
            ("&=", AmpEqual),
            ("|=", PipeEqual),
            ("^=", CaretEqual),
        ] {
            if tail.starts_with(text.as_bytes()) {
                return Some((text.len(), kind));
            }
        }
        let kind = match tail[0] {
            b'(' => LeftParen,
            b')' => RightParen,
            b'{' => LeftBrace,
            b'}' => RightBrace,
            b'[' => LeftBracket,
            b']' => RightBracket,
            b';' => Semicolon,
            b':' => Colon,
            b',' => Comma,
            b'.' => Dot,
            b'@' => At,
            b'+' => Plus,
            b'-' => Minus,
            b'*' => Star,
            b'/' => Slash,
            b'%' => Percent,
            b'&' => Amp,
            b'|' => Pipe,
            b'^' => Caret,
            b'!' => Bang,
            b'~' => Tilde,
            b'=' => Equal,
            b'<' => Less,
            b'>' => Greater,
            b'?' => Question,
            _ => return None,
        };
        Some((1, kind))
    }
}

fn is_ident_continue(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

//! Small bounded JSON reader for summary documents. Duplicate members are errors.
use std::collections::BTreeMap;

#[derive(Debug)]
pub(super) enum Json {
    Null,
    Bool(bool),
    Number(u64),
    String(String),
    Array(Vec<Json>),
    Object(BTreeMap<String, Json>),
}
pub(super) fn parse(text: &str) -> Result<Json, String> {
    if text.len() > 262_144 {
        return Err("summary exceeds the 256 KiB limit".into());
    }
    let mut parser = Parser {
        text,
        at: 0,
        nodes: 4096,
    };
    let value = parser.value(0)?;
    parser.space();
    if parser.at != text.len() {
        return Err(parser.error("trailing content"));
    }
    Ok(value)
}
struct Parser<'a> {
    text: &'a str,
    at: usize,
    nodes: usize,
}
impl Parser<'_> {
    fn error(&self, message: &str) -> String {
        format!("{message} at byte {}", self.at)
    }
    fn space(&mut self) {
        while self
            .text
            .as_bytes()
            .get(self.at)
            .is_some_and(|b| matches!(b, b' ' | b'\n' | b'\r' | b'\t'))
        {
            self.at += 1;
        }
    }
    fn eat(&mut self, byte: u8) -> bool {
        self.space();
        if self.text.as_bytes().get(self.at) == Some(&byte) {
            self.at += 1;
            true
        } else {
            false
        }
    }
    fn require(&mut self, byte: u8) -> Result<(), String> {
        if self.eat(byte) {
            Ok(())
        } else {
            Err(self.error("unexpected JSON token"))
        }
    }
    fn value(&mut self, depth: usize) -> Result<Json, String> {
        if depth > 32 || self.nodes == 0 {
            return Err(self.error("JSON resource limit exceeded"));
        }
        self.nodes -= 1;
        self.space();
        match self.text.as_bytes().get(self.at) {
            Some(b'"') => Ok(Json::String(self.string()?)),
            Some(b'{') => {
                self.at += 1;
                let mut members = BTreeMap::new();
                if !self.eat(b'}') {
                    loop {
                        let name = self.string()?;
                        self.require(b':')?;
                        let value = self.value(depth + 1)?;
                        if members.insert(name, value).is_some() {
                            return Err(self.error("duplicate JSON member"));
                        }
                        if self.eat(b'}') {
                            break;
                        }
                        self.require(b',')?;
                    }
                }
                Ok(Json::Object(members))
            }
            Some(b'[') => {
                self.at += 1;
                let mut items = Vec::new();
                if !self.eat(b']') {
                    loop {
                        items.push(self.value(depth + 1)?);
                        if self.eat(b']') {
                            break;
                        }
                        self.require(b',')?;
                    }
                }
                Ok(Json::Array(items))
            }
            Some(b'0'..=b'9') => {
                let start = self.at;
                self.at += 1;
                if self.text.as_bytes()[start] != b'0' {
                    while self
                        .text
                        .as_bytes()
                        .get(self.at)
                        .is_some_and(u8::is_ascii_digit)
                    {
                        self.at += 1;
                    }
                }
                self.text[start..self.at]
                    .parse()
                    .map(Json::Number)
                    .map_err(|_| self.error("integer overflow"))
            }
            _ => {
                for (word, value) in [
                    ("true", Json::Bool(true)),
                    ("false", Json::Bool(false)),
                    ("null", Json::Null),
                ] {
                    if self.text[self.at..].starts_with(word) {
                        self.at += word.len();
                        return Ok(value);
                    }
                }
                Err(self.error("expected JSON value"))
            }
        }
    }
    fn hex4(&mut self) -> Result<u16, String> {
        let bytes = self.text.as_bytes();
        let mut value = 0;
        for _ in 0..4 {
            let digit = match bytes.get(self.at) {
                Some(b'0'..=b'9') => bytes[self.at] - b'0',
                Some(b'a'..=b'f') => bytes[self.at] - b'a' + 10,
                Some(b'A'..=b'F') => bytes[self.at] - b'A' + 10,
                _ => return Err(self.error("invalid Unicode escape")),
            };
            value = value * 16 + u16::from(digit);
            self.at += 1;
        }
        Ok(value)
    }
    fn string(&mut self) -> Result<String, String> {
        self.require(b'"')?;
        let mut result = String::new();
        loop {
            let Some(ch) = self.text[self.at..].chars().next() else {
                return Err(self.error("unterminated string"));
            };
            self.at += ch.len_utf8();
            match ch {
                '"' => return Ok(result),
                '\\' => {
                    let Some(byte) = self.text.as_bytes().get(self.at).copied() else {
                        return Err(self.error("unfinished escape"));
                    };
                    self.at += 1;
                    result.push(match byte {
                        b'"' => '"',
                        b'\\' => '\\',
                        b'/' => '/',
                        b'b' => '\u{8}',
                        b'f' => '\u{c}',
                        b'n' => '\n',
                        b'r' => '\r',
                        b't' => '\t',
                        b'u' => {
                            let first = self.hex4()?;
                            let code = if (0xd800..=0xdbff).contains(&first) {
                                if !self.text[self.at..].starts_with("\\u") {
                                    return Err(self.error("missing low surrogate"));
                                }
                                self.at += 2;
                                let second = self.hex4()?;
                                if !(0xdc00..=0xdfff).contains(&second) {
                                    return Err(self.error("invalid low surrogate"));
                                }
                                0x10000
                                    + ((u32::from(first) - 0xd800) << 10)
                                    + (u32::from(second) - 0xdc00)
                            } else {
                                u32::from(first)
                            };
                            char::from_u32(code)
                                .ok_or_else(|| self.error("invalid Unicode scalar"))?
                        }
                        _ => return Err(self.error("invalid escape")),
                    });
                }
                ch if ch < ' ' => return Err(self.error("unescaped control character")),
                ch => result.push(ch),
            }
        }
    }
}

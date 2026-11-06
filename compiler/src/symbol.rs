use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Symbol(pub u32);

/// A compilation owns its symbols. AST/HIR names are small IDs, never copied strings.
#[derive(Debug, Default)]
pub struct Interner {
    values: Vec<Arc<str>>,
    indices: HashMap<Arc<str>, Symbol>,
}

impl Interner {
    pub fn intern(&mut self, value: &str) -> Symbol {
        if let Some(&symbol) = self.indices.get(value) {
            return symbol;
        }
        let symbol = Symbol(u32::try_from(self.values.len()).expect("symbol table exhausted"));
        let value: Arc<str> = Arc::from(value);
        self.values.push(Arc::clone(&value));
        self.indices.insert(value, symbol);
        symbol
    }

    pub fn get(&self, symbol: Symbol) -> &str {
        &self.values[symbol.0 as usize]
    }

    pub fn lookup(&self, name: &str) -> Option<Symbol> {
        self.indices.get(name).copied()
    }

    pub fn entries(&self) -> impl Iterator<Item = (Symbol, &str)> {
        self.values
            .iter()
            .enumerate()
            .map(|(index, text)| (Symbol(index as u32), text.as_ref()))
    }
}

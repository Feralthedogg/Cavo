use std::fmt::Write;

/// One function's SSA names and auxiliary labels. Scratch storage is always
/// hoisted to its entry, so repeated calls in a loop cannot grow the stack.
pub(super) struct Writer {
    pub text: String,
    pub allocations: String,
    pub label: String,
    next: u32,
}
impl Writer {
    pub fn new() -> Self {
        Self {
            text: String::new(),
            allocations: String::new(),
            label: "entry".into(),
            next: 0,
        }
    }
    pub fn line(&mut self, line: String) {
        let _ = writeln!(self.text, "  {line}");
    }
    pub fn temp(&mut self, expression: String) -> String {
        let name = format!("%v{}", self.next);
        self.next += 1;
        self.line(format!("{name} = {expression}"));
        name
    }
    pub fn fresh(&mut self, prefix: &str) -> String {
        let name = format!("{prefix}{}", self.next);
        self.next += 1;
        name
    }
    pub fn start(&mut self, label: &str) {
        let _ = writeln!(self.text, "{label}:");
        self.label = label.into();
    }
    pub fn offset(&mut self, base: &str, bytes: u64) -> String {
        if bytes == 0 {
            base.into()
        } else {
            self.temp(format!("getelementptr i8, ptr {base}, i64 {bytes}"))
        }
    }
    pub fn alloca(&mut self, bytes: u64, alignment: u64) -> String {
        let name = self.fresh("scratch");
        let _ = writeln!(
            self.allocations,
            "  %{name} = alloca [{} x i8], align {alignment}",
            bytes.max(1)
        );
        format!("%{name}")
    }
}

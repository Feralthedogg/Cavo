use crate::source::{FileId, SourceFile, SourceMap, Span};
use std::{collections::BTreeMap, fmt::Write};

pub(crate) fn report(diagnostics: &mut Vec<Diagnostic>, diagnostic: Diagnostic) {
    if diagnostics.len() < 100 {
        diagnostics.push(diagnostic);
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum MoveCertainty {
    Definite,
    Possible,
}

impl MoveCertainty {
    pub(crate) fn diagnostic(self, span: Span) -> Diagnostic {
        let (message, label) = match self {
            Self::Definite => (
                "value was moved before this use",
                "this place has already been moved",
            ),
            Self::Possible => (
                "value may have been moved before this use",
                "this place is not available on every incoming path",
            ),
        };
        Diagnostic::error("E-MOVE-USE", message, span)
            .primary_label(label)
            .help("use the new owner, or reinitialize this place before using it")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Label {
    pub span: Span,
    pub message: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Diagnostic {
    pub code: &'static str,
    pub message: String,
    pub primary: Span,
    pub primary_label: Option<String>,
    pub labels: Vec<Label>,
    pub notes: Vec<String>,
    pub helps: Vec<String>,
}

impl Diagnostic {
    pub fn error(code: &'static str, message: impl Into<String>, primary: Span) -> Self {
        Self {
            code,
            message: message.into(),
            primary,
            primary_label: None,
            labels: Vec::new(),
            notes: Vec::new(),
            helps: Vec::new(),
        }
    }

    pub fn primary_label(mut self, message: impl Into<String>) -> Self {
        self.primary_label = Some(message.into());
        self
    }

    pub fn label(mut self, span: Span, message: impl Into<String>) -> Self {
        self.labels.push(Label {
            span,
            message: message.into(),
        });
        self
    }

    pub fn note(mut self, message: impl Into<String>) -> Self {
        self.notes.push(message.into());
        self
    }

    pub fn help(mut self, message: impl Into<String>) -> Self {
        self.helps.push(message.into());
        self
    }

    pub fn render(&self, sources: &SourceMap) -> String {
        let mut output = format!("error[{}]: {}\n", self.code, self.message);
        let mut files: BTreeMap<FileId, Vec<Annotation<'_>>> = BTreeMap::new();
        files
            .entry(self.primary.file)
            .or_default()
            .push(Annotation {
                span: self.primary,
                message: self.primary_label.as_deref().unwrap_or(""),
                primary: true,
            });
        for label in &self.labels {
            files.entry(label.span.file).or_default().push(Annotation {
                span: label.span,
                message: &label.message,
                primary: false,
            });
        }
        let primary = files
            .remove(&self.primary.file)
            .expect("primary source group");
        let width = render_source(
            &mut output,
            sources.file(self.primary.file),
            &primary,
            "-->",
        );
        for (file, annotations) in files {
            render_source(&mut output, sources.file(file), &annotations, ":::");
        }
        let indent = " ".repeat(width + 1);
        if !self.notes.is_empty() || !self.helps.is_empty() {
            let _ = writeln!(output, "{indent}|");
        }
        for note in &self.notes {
            render_message(&mut output, &indent, "note", note);
        }
        for help in &self.helps {
            render_message(&mut output, &indent, "help", help);
        }
        output.push('\n');
        output
    }
}

struct Annotation<'a> {
    span: Span,
    message: &'a str,
    primary: bool,
}

struct Marker<'a> {
    start: usize,
    end: usize,
    message: &'a str,
    primary: bool,
}

fn source_lines<'a>(
    source: &SourceFile,
    annotations: &[Annotation<'a>],
) -> BTreeMap<usize, Vec<Marker<'a>>> {
    let mut lines: BTreeMap<usize, Vec<Marker<'_>>> = BTreeMap::new();
    for annotation in annotations {
        let span = annotation.span;
        let (first, start) = source.location(span.start);
        let (after, end) = source.location(span.end.max(span.start));
        let last_offset = if span.end > span.start {
            span.end - 1
        } else {
            span.start
        };
        let (last, _) = source.location(last_offset);
        // Keep large spans bounded while still showing their start and end.
        let shown: Vec<_> = if last - first < 4 {
            (first..=last).collect()
        } else {
            vec![first, last]
        };
        for line in shown {
            lines.entry(line).or_default().push(Marker {
                start: if line == first { start - 1 } else { 0 },
                end: if line == after { end - 1 } else { usize::MAX },
                message: if line == last { annotation.message } else { "" },
                primary: annotation.primary,
            });
        }
    }
    lines
}

fn render_source(
    output: &mut String,
    source: &SourceFile,
    annotations: &[Annotation<'_>],
    arrow: &str,
) -> usize {
    let lines = source_lines(source, annotations);
    let width = lines
        .last_key_value()
        .expect("annotated source line")
        .0
        .to_string()
        .len();
    let (line, column) = source.location(annotations[0].span.start);
    let _ = writeln!(
        output,
        "{:width$}{arrow} {}:{line}:{column}",
        "",
        source.path.display()
    );
    let _ = writeln!(output, "{:width$} |", "");
    let mut previous = None;
    for (line, mut markers) in lines {
        if previous.is_some_and(|previous| line > previous + 1) {
            let _ = writeln!(output, "{:width$} ...", "");
        }
        let rendered = RenderedLine::new(source.line(line));
        let _ = writeln!(output, "{line:>width$} | {}", rendered.text);
        markers.sort_by_key(|marker| (marker.start, !marker.primary));
        for marker in markers {
            let start = rendered.column(marker.start);
            let end = rendered.column(marker.end);
            let mark = if marker.primary { "^" } else { "-" };
            let _ = write!(
                output,
                "{:width$} | {}{}",
                "",
                " ".repeat(start),
                mark.repeat(end.saturating_sub(start).max(1))
            );
            if !marker.message.is_empty() {
                let _ = write!(output, " {}", marker.message);
            }
            output.push('\n');
        }
        previous = Some(line);
    }
    width
}

// Map Unicode scalar columns to the displayed snippet after expanding tabs and
// escaping control characters. This does not implement terminal grapheme width.
struct RenderedLine {
    text: String,
    columns: Vec<usize>,
}

impl RenderedLine {
    fn new(source: &str) -> Self {
        let mut text = String::new();
        let mut columns = vec![0];
        let mut column = 0;
        for character in source.chars() {
            if character == '\t' {
                let spaces = 4 - column % 4;
                text.extend(std::iter::repeat_n(' ', spaces));
                column += spaces;
            } else if character.is_control() {
                let escaped = character.escape_default().to_string();
                column += escaped.len();
                text.push_str(&escaped);
            } else {
                text.push(character);
                column += 1;
            }
            columns.push(column);
        }
        Self { text, columns }
    }
    fn column(&self, scalar: usize) -> usize {
        self.columns[scalar.min(self.columns.len() - 1)]
    }
}

fn render_message(output: &mut String, indent: &str, kind: &str, message: &str) {
    let mut lines = message.lines();
    let _ = writeln!(output, "{indent}= {kind}: {}", lines.next().unwrap_or(""));
    let continuation = " ".repeat(kind.len() + 4);
    for line in lines {
        let _ = writeln!(output, "{indent}{continuation}{line}");
    }
}

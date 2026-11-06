use std::path::{Path, PathBuf};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct FileId(pub u32);

/// Half-open UTF-8 byte range. Offsets always refer to the original source.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Span {
    pub file: FileId,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: FileId, start: u32, end: u32) -> Self {
        Self { file, start, end }
    }

    pub fn join(self, other: Self) -> Self {
        debug_assert_eq!(self.file, other.file);
        Self::new(
            self.file,
            self.start.min(other.start),
            self.end.max(other.end),
        )
    }
}

#[derive(Debug)]
pub struct SourceFile {
    pub id: FileId,
    pub path: PathBuf,
    text: String,
    line_starts: Vec<u32>,
}

impl SourceFile {
    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn slice(&self, span: Span) -> &str {
        assert_eq!(self.id, span.file);
        &self.text[span.start as usize..span.end as usize]
    }

    /// One-based line and Unicode scalar column (not terminal display width).
    pub fn location(&self, offset: u32) -> (usize, usize) {
        let mut offset = (offset as usize).min(self.text.len());
        while !self.text.is_char_boundary(offset) {
            offset -= 1;
        }
        let line = self
            .line_starts
            .partition_point(|&start| start as usize <= offset)
            - 1;
        let start = self.line_starts[line] as usize;
        let column = self.text[start..offset].chars().count() + 1;
        (line + 1, column)
    }

    pub fn line(&self, one_based: usize) -> &str {
        let Some(&start) = self.line_starts.get(one_based.saturating_sub(1)) else {
            return "";
        };
        let end = self
            .line_starts
            .get(one_based)
            .map_or(self.text.len(), |&n| n as usize);
        self.text[start as usize..end].trim_end_matches(['\r', '\n'])
    }
}

#[derive(Debug, Default)]
pub struct SourceMap {
    files: Vec<SourceFile>,
}

impl SourceMap {
    pub fn add(&mut self, path: impl AsRef<Path>, text: String) -> Result<FileId, &'static str> {
        if text.len() > u32::MAX as usize || self.files.len() >= u32::MAX as usize {
            return Err("source exceeds the 32-bit source map limit");
        }
        let id = FileId(self.files.len() as u32);
        let mut line_starts = vec![0];
        line_starts.extend(
            text.bytes()
                .enumerate()
                .filter_map(|(i, b)| (b == b'\n').then_some((i + 1) as u32)),
        );
        self.files.push(SourceFile {
            id,
            path: path.as_ref().to_owned(),
            text,
            line_starts,
        });
        Ok(id)
    }

    pub fn file(&self, id: FileId) -> &SourceFile {
        &self.files[id.0 as usize]
    }

    pub fn files(&self) -> &[SourceFile] {
        &self.files
    }
}

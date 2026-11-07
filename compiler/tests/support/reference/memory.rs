use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Pointer {
    pub allocation: usize,
    generation: u64,
    pub offset: u64,
    path: usize,
    pub(super) unions: Vec<(u64, hir::DefId, u32)>,
}

impl Pointer {
    pub(super) fn same_address(&self, other: &Self) -> bool {
        self.allocation == other.allocation
            && self.generation == other.generation
            && self.offset == other.offset
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Atom {
    Pointer(Option<Pointer>),
    Function(hir::DefId),
    Metadata(Metadata),
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Kind {
    Stack,
    Heap,
    Static,
}
struct Allocation {
    generation: u64,
    alive: bool,
    kind: Kind,
    bytes: Vec<u8>,
    initialized: Vec<bool>,
    atoms: HashMap<u64, Atom>,
    zero: HashSet<usize>,
    tasks: HashMap<usize, usize>,
}

pub struct Memory {
    allocations: Vec<Allocation>,
    paths: HashMap<(usize, u64), usize>,
    parents: Vec<Option<usize>>,
    dropped: HashSet<(usize, u64, usize, hir::DefId)>,
    bytes: usize,
    max_bytes: usize,
    max_objects: usize,
}

impl Memory {
    pub fn new(max_bytes: usize, max_objects: usize) -> Self {
        Self {
            allocations: Vec::new(),
            paths: HashMap::new(),
            parents: vec![None],
            dropped: HashSet::new(),
            bytes: 0,
            max_bytes,
            max_objects,
        }
    }

    pub fn stack(&mut self, size: u64) -> Result<Pointer> {
        self.allocate(size, Kind::Stack)
    }
    pub fn heap(&mut self, size: u64) -> Result<Pointer> {
        self.allocate(size, Kind::Heap)
    }

    fn allocate(&mut self, size: u64, kind: Kind) -> Result<Pointer> {
        let size = usize::try_from(size).map_err(|_| Error::Limit("allocation size"))?;
        let total = self
            .bytes
            .checked_add(size)
            .ok_or(Error::Limit("allocation bytes"))?;
        if total > self.max_bytes || self.allocations.len() >= self.max_objects {
            return Err(Error::Limit("memory budget"));
        }
        let pointer = Pointer {
            allocation: self.allocations.len(),
            generation: 1,
            offset: 0,
            path: 0,
            unions: Vec::new(),
        };
        self.allocations.push(Allocation {
            generation: 1,
            alive: true,
            kind,
            bytes: vec![0; size],
            initialized: vec![false; size],
            atoms: HashMap::new(),
            zero: HashSet::new(),
            tasks: HashMap::new(),
        });
        self.bytes = total;
        Ok(pointer)
    }

    pub(super) fn literal(&mut self, bytes: &[u8]) -> Result<Pointer> {
        let pointer = self.allocate(bytes.len() as u64, Kind::Static)?;
        let allocation = &mut self.allocations[pointer.allocation];
        allocation.bytes.copy_from_slice(bytes);
        allocation.initialized.fill(true);
        Ok(pointer)
    }

    pub fn free(&mut self, pointer: &Pointer) -> Result<()> {
        let allocation = self.allocation(pointer)?;
        if allocation.kind != Kind::Heap || pointer.offset != 0 {
            return Err(Error::Undefined("invalid deallocation"));
        }
        self.end(pointer)
    }

    pub(super) fn end_stack(&mut self, pointer: &Pointer) -> Result<()> {
        if self.allocation(pointer)?.kind != Kind::Stack {
            return Err(Error::Undefined("invalid stack lifetime"));
        }
        self.end(pointer)
    }

    fn end(&mut self, pointer: &Pointer) -> Result<()> {
        let allocation = &mut self.allocations[pointer.allocation];
        self.bytes -= allocation.bytes.len();
        allocation.alive = false;
        allocation.generation += 1;
        allocation.bytes = Vec::new();
        allocation.initialized = Vec::new();
        allocation.atoms = HashMap::new();
        allocation.zero = HashSet::new();
        allocation.tasks = HashMap::new();
        Ok(())
    }

    fn allocation(&self, pointer: &Pointer) -> Result<&Allocation> {
        let allocation = self
            .allocations
            .get(pointer.allocation)
            .ok_or(Error::Undefined("forged pointer provenance"))?;
        if !allocation.alive || allocation.generation != pointer.generation {
            return Err(Error::Undefined("use after free or storage lifetime end"));
        }
        Ok(allocation)
    }

    fn range(&self, pointer: &Pointer, size: u64) -> Result<std::ops::Range<usize>> {
        let allocation = self.allocation(pointer)?;
        let end = pointer
            .offset
            .checked_add(size)
            .ok_or(Error::Undefined("out of bounds"))?;
        if end > allocation.bytes.len() as u64 {
            return Err(Error::Undefined("out of bounds"));
        }
        Ok(pointer.offset as usize..end as usize)
    }

    pub(super) fn check(&self, pointer: &Pointer, size: u64, alignment: u64) -> Result<()> {
        self.range(pointer, size)?;
        if alignment == 0 || !pointer.offset.is_multiple_of(alignment) {
            return Err(Error::Undefined("misaligned access"));
        }
        Ok(())
    }

    pub fn read_bytes(&self, pointer: &Pointer, size: u64) -> Result<Vec<u8>> {
        let range = self.range(pointer, size)?;
        let allocation = &self.allocations[pointer.allocation];
        if !allocation.initialized[range.clone()]
            .iter()
            .all(|&byte| byte)
        {
            return Err(Error::Undefined("uninitialized or moved value"));
        }
        Ok(allocation.bytes[range].to_vec())
    }

    pub fn write_bytes(&mut self, pointer: &Pointer, bytes: &[u8]) -> Result<()> {
        let range = self.range(pointer, bytes.len() as u64)?;
        let allocation = &mut self.allocations[pointer.allocation];
        if allocation.kind == Kind::Static {
            return Err(Error::Undefined("write to read-only storage"));
        }
        allocation.atoms.retain(|&offset, _| {
            offset.saturating_add(8) <= range.start as u64 || offset >= range.end as u64
        });
        allocation.bytes[range.clone()].copy_from_slice(bytes);
        allocation.initialized[range].fill(true);
        Ok(())
    }

    pub(super) fn invalidate(&mut self, pointer: &Pointer, size: u64) -> Result<()> {
        let range = self.range(pointer, size)?;
        let parents = &self.parents;
        let allocation = &mut self.allocations[pointer.allocation];
        allocation.initialized[range.clone()].fill(false);
        allocation
            .atoms
            .retain(|&offset, _| offset < range.start as u64 || offset >= range.end as u64);
        allocation
            .zero
            .retain(|&path| !descends(parents, path, pointer.path));
        allocation
            .tasks
            .retain(|&path, _| !descends(parents, path, pointer.path));
        Ok(())
    }

    pub(super) fn child(&mut self, pointer: &Pointer, bytes: u64, step: u64) -> Result<Pointer> {
        self.allocation(pointer)?;
        let path = if let Some(&path) = self.paths.get(&(pointer.path, step)) {
            path
        } else {
            if self.parents.len() >= self.max_objects {
                return Err(Error::Limit("subobject path budget"));
            }
            let path = self.parents.len();
            self.parents.push(Some(pointer.path));
            self.paths.insert((pointer.path, step), path);
            path
        };
        Ok(Pointer {
            offset: pointer
                .offset
                .checked_add(bytes)
                .ok_or(Error::Undefined("pointer offset overflow"))?,
            path,
            ..pointer.clone()
        })
    }

    pub(super) fn offset(&self, pointer: &Pointer, bytes: u64) -> Result<Pointer> {
        self.allocation(pointer)?;
        Ok(Pointer {
            offset: pointer
                .offset
                .checked_add(bytes)
                .ok_or(Error::Undefined("pointer offset overflow"))?,
            ..pointer.clone()
        })
    }

    pub(super) fn atom(&self, pointer: &Pointer) -> Result<&Atom> {
        self.read_bytes(pointer, 8)?;
        self.allocations[pointer.allocation]
            .atoms
            .get(&pointer.offset)
            .ok_or(Error::Undefined("missing pointer or callable provenance"))
    }

    pub(super) fn write_atom(&mut self, pointer: &Pointer, atom: Atom) -> Result<()> {
        self.write_bytes(pointer, &[0; 8])?;
        self.allocations[pointer.allocation]
            .atoms
            .insert(pointer.offset, atom);
        Ok(())
    }

    pub(super) fn zero_initialized(&self, pointer: &Pointer) -> Result<bool> {
        self.range(pointer, 0)?;
        Ok(self.allocations[pointer.allocation]
            .zero
            .contains(&pointer.path))
    }
    pub(super) fn initialize_zero(&mut self, pointer: &Pointer) -> Result<()> {
        self.range(pointer, 0)?;
        self.allocations[pointer.allocation]
            .zero
            .insert(pointer.path);
        Ok(())
    }
    pub(super) fn task(&self, pointer: &Pointer) -> Result<usize> {
        self.range(pointer, 0)?;
        self.allocations[pointer.allocation]
            .tasks
            .get(&pointer.path)
            .copied()
            .ok_or(Error::Undefined("uninitialized or moved task handle"))
    }
    pub(super) fn write_task(&mut self, pointer: &Pointer, task: usize) -> Result<()> {
        self.initialize_zero(pointer)?;
        self.allocations[pointer.allocation]
            .tasks
            .insert(pointer.path, task);
        Ok(())
    }
    pub(super) fn reinitialize(&mut self, pointer: &Pointer, ty: hir::DefId, zero: bool) {
        self.dropped.remove(&(
            pointer.allocation,
            pointer.offset,
            if zero { pointer.path } else { 0 },
            ty,
        ));
    }
    pub(super) fn note_drop(
        &mut self,
        pointer: &Pointer,
        ty: hir::DefId,
        zero: bool,
    ) -> Result<()> {
        self.allocation(pointer)?;
        if !self.dropped.insert((
            pointer.allocation,
            pointer.offset,
            if zero { pointer.path } else { 0 },
            ty,
        )) {
            return Err(Error::Undefined("double drop"));
        }
        Ok(())
    }
}

fn descends(parents: &[Option<usize>], mut path: usize, ancestor: usize) -> bool {
    loop {
        if path == ancestor {
            return true;
        }
        let Some(parent) = parents[path] else {
            return false;
        };
        path = parent;
    }
}

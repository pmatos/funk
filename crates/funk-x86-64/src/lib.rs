//! `funk-x86-64`: funk's naive x86-64 backend for Linux
//! (ADR-2026-10-30-1228).
//!
//! [`compile`] lowers a valid module to two assembly files in GNU `as`'s
//! AT&T syntax (ADR-2026-10-30-1229). The module's file holds one function
//! per fir function, each a global symbol that follows the System V AMD64
//! calling convention (ADR-2026-10-30-1232), so C code can link to it. The
//! entry file holds the entry point of an executable that runs one function
//! from the command line and prints its results (ADR-2026-10-30-1233).
//! [`build`] assembles both with `as` and links them with `ld` into an
//! object file and an executable (ADR-2026-10-30-1326).
//!
//! Register allocation is the baseline: every value has a stack slot, and
//! each op loads its operands and stores its results (ADR-2026-10-30-1230).
//! The backend lowers `i1`, `i8`, `i16`, `i32` and `i64`
//! (ADR-2026-10-30-1231), and functions with at most one result (#31).
//! Anything else is reported as a [`Diagnostic`] that carries the IR
//! location of the op, or of the block for a parameter.
//!
//! Each op family's lowering lives in a file of its own in `lower/`.

pub mod abi;
pub mod asm;
mod entry;
pub mod frame;
mod lower;
mod tools;
pub mod width;

use std::ffi::OsString;
use std::path::{Path, PathBuf};

use funk_ir::{Diagnostic, Module};

/// The assembly of a module: the module's functions, and the entry point
/// of an executable that runs them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Program {
    /// The module's functions: the text of the object file.
    pub module: String,
    /// The runtime, a wrapper for each function and the table of functions.
    pub entry: String,
}

/// Lowers `m`, which must be valid, or reports every part of it that the
/// backend cannot lower.
pub fn compile(m: &Module) -> Result<Program, Vec<Diagnostic>> {
    let lowered = lower::module(m)?;
    let entry = entry::generate(m, &lowered.frames)?;
    Ok(Program {
        module: lowered.text,
        entry,
    })
}

/// Why a module was not built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BuildError {
    /// The backend cannot lower these parts of the module.
    Unsupported(Vec<Diagnostic>),
    /// The assembler or the linker could not run, failed or printed
    /// something.
    Tool(String),
    /// A file or directory could not be created, written or moved into
    /// place.
    Io(String),
}

/// The files that [`build`] writes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Outputs {
    /// The object file of the module's functions: the executable's path
    /// with `.o` added.
    pub object: PathBuf,
    /// The executable.
    pub executable: PathBuf,
}

/// The path of the object file that goes with the executable `exe`: `exe`
/// with `.o` added, so `out/add` gives `out/add.o`.
pub fn object_path(exe: &Path) -> PathBuf {
    let mut s = OsString::from(exe.as_os_str());
    s.push(".o");
    PathBuf::from(s)
}

/// Compiles `m`, which must be valid, then writes its object file and the
/// executable `exe`, linked from that object file and the entry point.
///
/// Every file is first written to a temporary directory next to `exe`. The
/// object file and then the executable are moved into place only once both
/// are built, so a build that fails leaves both paths as they were. The one
/// exception: if the executable cannot be moved into place, the new object
/// file is removed again.
pub fn build(m: &Module, exe: &Path) -> Result<Outputs, BuildError> {
    let program = compile(m).map_err(BuildError::Unsupported)?;
    let object = object_path(exe);
    let parent = match exe.parent() {
        Some(p) if !p.as_os_str().is_empty() => p,
        _ => Path::new("."),
    };
    let tmp = tools::TempDir::new_in(parent).map_err(BuildError::Io)?;
    let [module_s, entry_s, entry_o, built_o, built_exe] =
        ["module.s", "entry.s", "entry.o", "out.o", "out"].map(|n| tmp.join(n));
    let write = |path: &Path, text: &str| {
        std::fs::write(path, text)
            .map_err(|e| BuildError::Io(format!("cannot write {}: {e}", path.display())))
    };
    write(&module_s, &program.module)?;
    write(&entry_s, &program.entry)?;
    tools::assemble(&module_s, &built_o)
        .and_then(|()| tools::assemble(&entry_s, &entry_o))
        .and_then(|()| tools::link(&[&built_o, &entry_o], &built_exe))
        .map_err(BuildError::Tool)?;
    let place = |from: &Path, to: &Path| {
        std::fs::rename(from, to)
            .map_err(|e| BuildError::Io(format!("cannot write {}: {e}", to.display())))
    };
    place(&built_o, &object)?;
    if let Err(e) = place(&built_exe, exe) {
        let _ = std::fs::remove_file(&object);
        return Err(e);
    }
    Ok(Outputs {
        object,
        executable: exe.to_path_buf(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_object_file_is_named_after_the_executable() {
        assert_eq!(object_path(Path::new("out/add")), Path::new("out/add.o"));
        assert_eq!(object_path(Path::new("a.out")), Path::new("a.out.o"));
    }
}

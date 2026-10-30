//! Running GNU `as` and `ld` (ADR-2026-10-30-1229), and the temporary directory that
//! holds what they read and write on the way to the outputs.
//!
//! `as` and `ld` are told the target, x86-64, on their command lines, so a
//! default from their configuration or the environment, such as
//! `LDEMULATION`, does not change what they build.

use std::path::{Path, PathBuf};
use std::process::Command;

/// Assembles the file `source` into the object file `object`.
pub fn assemble(source: &Path, object: &Path) -> Result<(), String> {
    let mut cmd = Command::new("as");
    cmd.arg("--64")
        .arg("-o")
        .arg(operand(object))
        .arg(operand(source));
    run("the assembler, as", cmd)
}

/// Links `objects` into the static x86-64 executable `exe`, whose entry
/// point is the runtime's `__funk_start`.
pub fn link(objects: &[&Path], exe: &Path) -> Result<(), String> {
    let mut cmd = Command::new("ld");
    cmd.args(["-m", "elf_x86_64", "-static"])
        .arg("-o")
        .arg(operand(exe))
        .arg("-e")
        .arg("__funk_start");
    cmd.args(objects.iter().map(|o| operand(o)));
    run("the linker, ld", cmd)
}

/// `path` as a tool's operand: a relative path that starts with `-` gets
/// `./` in front, so the tool does not read it as an option.
fn operand(path: &Path) -> PathBuf {
    if path.as_os_str().as_encoded_bytes().starts_with(b"-") {
        Path::new(".").join(path)
    } else {
        path.to_path_buf()
    }
}

/// Runs a tool. It fails when it cannot start, when it exits with an
/// error, and when it prints anything, such as a warning.
fn run(what: &str, mut cmd: Command) -> Result<(), String> {
    let out = cmd.output().map_err(|e| {
        if e.kind() == std::io::ErrorKind::NotFound {
            format!("cannot run {what}: it is not installed; funk build needs GNU binutils")
        } else {
            format!("cannot run {what}: {e}")
        }
    })?;
    let said: Vec<String> = [&out.stderr, &out.stdout]
        .iter()
        .map(|b| String::from_utf8_lossy(b).trim().replace('\n', " | "))
        .filter(|s| !s.is_empty())
        .collect();
    let said = said.join(" | ");
    match (out.status.success(), said.is_empty()) {
        (true, true) => Ok(()),
        (true, false) => Err(format!("{what} warned: {said}")),
        (false, _) => Err(format!("{what} failed ({}): {said}", out.status)),
    }
}

/// A new, empty directory, removed with everything in it when dropped.
#[derive(Debug)]
pub struct TempDir(PathBuf);

impl TempDir {
    /// Creates a hidden directory in `base`, with a name that nothing uses
    /// yet, readable only by its owner.
    pub fn new_in(base: &Path) -> Result<TempDir, String> {
        let mut builder = std::fs::DirBuilder::new();
        #[cfg(unix)]
        std::os::unix::fs::DirBuilderExt::mode(&mut builder, 0o700);
        let mut n = 0u32;
        loop {
            let dir = base.join(format!(".funk-build.{}.{n}", std::process::id()));
            match builder.create(&dir) {
                Ok(()) => return Ok(TempDir(dir)),
                Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists && n < 9999 => n += 1,
                Err(e) => {
                    return Err(format!(
                        "cannot create a temporary directory in {}: {e}",
                        base.display()
                    ));
                }
            }
        }
    }

    /// The path of `name` in the directory.
    pub fn join(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn temporary_directories_are_fresh_and_removed() {
        let base = std::env::temp_dir();
        let a = TempDir::new_in(&base).unwrap();
        let b = TempDir::new_in(&base).unwrap();
        assert_ne!(a.0, b.0);
        assert_eq!(a.0.parent(), Some(base.as_path()));
        std::fs::write(a.join("x"), "x").unwrap();
        let path = a.0.clone();
        drop(a);
        assert!(!path.exists());
        let missing = base.join("funk-no-such-directory").join("x");
        let err = TempDir::new_in(&missing).unwrap_err();
        assert!(err.contains("cannot create a temporary directory"), "{err}");
    }

    #[test]
    fn paths_that_start_with_a_dash_are_not_options() {
        assert_eq!(operand(Path::new("-x")), Path::new("./-x"));
        assert_eq!(operand(Path::new("out/-x")), Path::new("out/-x"));
        assert_eq!(operand(Path::new("/tmp/-x")), Path::new("/tmp/-x"));
    }

    #[test]
    fn a_missing_tool_is_reported() {
        let err = run("the tool", Command::new("funk-no-such-tool")).unwrap_err();
        assert!(err.contains("not installed"), "{err}");
    }
}

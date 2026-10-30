//! Helpers shared by the tests of the `funk` binary.

#![allow(dead_code)]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

pub const SEVEN: &str = "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

/// A fresh, empty directory for one test.
pub fn dir(name: &str) -> PathBuf {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(name);
    if dir.exists() {
        restore_permissions(&dir);
        std::fs::remove_dir_all(&dir).unwrap();
    }
    std::fs::create_dir_all(&dir).unwrap();
    dir
}

/// Makes a directory left read-only by an earlier run removable again.
fn restore_permissions(dir: &Path) {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let _ = std::fs::set_permissions(dir, std::fs::Permissions::from_mode(0o755));
    }
}

/// Writes `text` to a fresh file named `name` and returns its path.
pub fn file(name: &str, text: &str) -> String {
    let dir = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("cli");
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, text).unwrap();
    path.to_string_lossy().into_owned()
}

/// Runs funk with `args` in the current directory and `stdin` as input.
pub fn funk(args: &[&str], stdin: &str) -> Output {
    funk_in(Path::new("."), args, stdin)
}

/// Runs funk with `args` in the directory `cwd`.
pub fn funk_in(cwd: &Path, args: &[&str], stdin: &str) -> Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_funk"))
        .current_dir(cwd)
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(stdin.as_bytes())
        .unwrap();
    child.wait_with_output().unwrap()
}

pub fn text(bytes: &[u8]) -> String {
    String::from_utf8(bytes.to_vec()).unwrap()
}

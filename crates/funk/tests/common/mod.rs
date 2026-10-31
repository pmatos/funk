//! Helpers shared by the tests of the `funk` binary.

#![allow(dead_code)]

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};

pub const SEVEN: &str = "func @seven() -> i32 {\n^entry:\n  %c: i32 = const 7 @0\n  ret %c @0\n}\n\nlocs {\n  @0 = unknown\n}\n";

/// A module that parses, with a block that validation rejects as
/// unreachable.
pub const DEAD: &str = "func @f() -> i32 {\n^entry:\n  %c: i32 = const 0 @0\n  ret %c @0\n^dead:\n  %d: i32 = const 1 @1\n  ret %d @1\n}\n\nlocs {\n  @0 = unknown\n  @1 = \"f.c\":3:1 to 3:9\n}\n";

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

/// A module whose functions are `funcs`, each with its ops at `@0`.
pub fn module(funcs: &[String]) -> String {
    let mut text = String::new();
    for f in funcs {
        text.push_str(f);
        text.push('\n');
    }
    text + "locs {\n  @0 = unknown\n}\n"
}

/// The text of `func @name(params) -> results` with one block of `ops`.
pub fn func(name: &str, params: &str, results: &str, ops: &[&str]) -> String {
    let arrow = if results.is_empty() {
        String::new()
    } else {
        format!(" -> {results}")
    };
    let mut text = format!("func @{name}({params}){arrow} {{\n^entry:\n");
    for op in ops {
        text.push_str(&format!("  {op} @0\n"));
    }
    text + "}\n"
}

/// Writes the module `fir` to a fresh directory named after `name` and
/// runs `funk build` on it with the options `extra`. Returns the output,
/// the executable's path and the source's.
pub fn try_build(name: &str, fir: &str, extra: &[&str]) -> (Output, String, String) {
    let dir = dir(&format!("build-{name}"));
    let src = dir
        .join(format!("{name}.fir"))
        .to_string_lossy()
        .into_owned();
    std::fs::write(&src, fir).unwrap();
    let exe = dir.join(name).to_string_lossy().into_owned();
    let mut args = vec!["build"];
    args.extend(extra);
    args.extend(["-o", &exe, &src]);
    (funk(&args, ""), exe, src)
}

/// Builds the module `fir` as [`try_build`] does, and returns the
/// executable's path. Panics if the build fails.
pub fn build(name: &str, fir: &str) -> PathBuf {
    let (out, exe, _) = try_build(name, fir, &[]);
    assert_eq!(
        out.status.code(),
        Some(0),
        "{}{}",
        text(&out.stdout),
        text(&out.stderr)
    );
    PathBuf::from(exe)
}

/// Runs a built executable with `args`.
pub fn run(exe: &Path, args: &[&str]) -> Output {
    Command::new(exe).args(args).output().unwrap()
}

/// The JSON line a built executable prints for `values`.
pub fn values(values: &[&str]) -> String {
    let quoted: Vec<String> = values.iter().map(|v| format!("\"{v}\"")).collect();
    format!("{{\"values\":[{}]}}\n", quoted.join(","))
}

/// Runs `exe` with `args` and checks that it prints `expected`.
pub fn expect(exe: &Path, args: &[&str], expected: &[&str]) {
    let out = run(exe, args);
    assert_eq!(
        (out.status.code(), text(&out.stdout), text(&out.stderr)),
        (Some(0), values(expected), String::new()),
        "{} {args:?}",
        exe.display()
    );
}

/// The boundary values of `iW`, read as signed integers: 0, 1, -1, the
/// minimum and the maximum, or at `i1` `false` (0) and `true` (-1).
pub fn boundaries(w: u32) -> Vec<i128> {
    if w == 1 {
        return vec![0, -1];
    }
    let min = -(1i128 << (w - 1));
    vec![0, 1, -1, min, -min - 1]
}

/// The spelling of a value of `iW` in fir and on the command line.
pub fn spell(w: u32, v: i128) -> String {
    match (w, v & 1) {
        (1, 1) => "true".into(),
        (1, _) => "false".into(),
        _ => v.to_string(),
    }
}

/// `x` wrapped to `w` bits, read as signed. `w` is at most 64.
pub fn wrap(w: u32, x: i128) -> i128 {
    let m = 1i128 << w;
    let s = x.rem_euclid(m);
    if s >= m / 2 { s - m } else { s }
}

/// Runs `exe` with `args` and checks that it prints one value of `iW`,
/// whichever it is: the result where the source's is poison.
pub fn expect_any(exe: &Path, args: &[&str], w: u32) {
    let out = run(exe, args);
    let stdout = text(&out.stdout);
    let value = stdout
        .strip_prefix("{\"values\":[\"")
        .and_then(|s| s.strip_suffix("\"]}\n"));
    let of_type = value.is_some_and(|v| match w {
        1 => v == "true" || v == "false",
        _ => v.parse::<i128>().is_ok_and(|x| wrap(w, x) == x),
    });
    assert!(
        out.status.code() == Some(0) && out.stderr.is_empty() && of_type,
        "{} {args:?}: {stdout}{}",
        exe.display(),
        text(&out.stderr)
    );
}

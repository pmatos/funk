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

/// The bits of each float value that a built executable printed in
/// `stdout`, one JSON line of values, each a float's bits read as a signed
/// integer, masked to `mask`.
pub fn float_bits(stdout: &str, mask: u64) -> Vec<u64> {
    stdout
        .trim_end()
        .strip_prefix("{\"values\":[")
        .and_then(|s| s.strip_suffix("]}"))
        .expect("a JSON line of values")
        .split(',')
        .map(|v| v.trim_matches('"').parse::<i64>().expect("a float's bits") as u64 & mask)
        .collect()
}

/// A small generator of random bits, so that every run checks the same
/// values.
pub struct Bits(pub u64);

impl Bits {
    pub fn next(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        self.0
    }

    pub fn wide(&mut self) -> u128 {
        (u128::from(self.next()) << 64) | u128::from(self.next())
    }
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

/// Runs `exe` with `args` and checks that it prints one value of `i128`,
/// whichever it is: the result where the source's is poison.
pub fn expect_some_i128(exe: &Path, args: &[&str]) {
    let out = run(exe, args);
    let stdout = text(&out.stdout);
    let value = stdout
        .strip_prefix("{\"values\":[\"")
        .and_then(|s| s.strip_suffix("\"]}\n"));
    assert!(
        out.status.code() == Some(0)
            && out.stderr.is_empty()
            && value.is_some_and(|v| v.parse::<i128>().is_ok()),
        "{} {args:?}: {stdout}{}",
        exe.display(),
        text(&out.stderr)
    );
}

/// Checks one run of a function that returns an `i128`: the exact result,
/// or any value where it is poison.
pub fn check_i128(exe: &Path, args: &[&str], result: Option<i128>) {
    match result {
        Some(r) => expect(exe, args, &[&r.to_string()]),
        None => expect_some_i128(exe, args),
    }
}

/// Checks how funk exits when it cannot write standard error, with `run`
/// starting it that way on its arguments: with 2 when it has a diagnostic
/// to write there, as `fir-ref` does, and with its verdict when it has
/// none. `name` names the files that the runs read and write.
pub fn check_unwritable_stderr(name: &str, run: impl Fn(&[&str]) -> Output) {
    let seven = file(&format!("{name}-seven.fir"), SEVEN);
    let bad = file(&format!("{name}-bad.fir"), "func @f(\n");
    let dead = file(&format!("{name}-dead.fir"), DEAD);
    let out = dir(name).join("out");
    let out = out.to_str().unwrap();
    for (args, status) in [
        (&["fmt", &bad][..], 2),
        (&["fmt", "--check", &bad], 2),
        (&["verify", &bad], 2),
        (&["verify", &dead], 2),
        (&["build", "-o", out, &bad], 2),
        (&["build", "-o", out, &dead], 2),
        (&["fmt", "--json", &bad], 1),
        (&["verify", "--json", &bad], 1),
        (&["build", "--json", "-o", out, &dead], 1),
        (&["fmt", &dead], 0),
        (&["verify", &seven], 0),
        (&["--version"], 0),
    ] {
        let ran = run(args);
        assert_eq!(ran.status.code(), Some(status), "{args:?}");
    }
}

/// The hard bit patterns of `f32`, which the native float tests share.
pub const F32: [u32; 14] = [
    0x0000_0000, // +0
    0x8000_0000, // -0
    0x0000_0001, // the smallest subnormal
    0x8000_0001,
    0x007f_ffff, // the largest subnormal
    0x3f80_0000, // 1.0
    0xbf80_0000, // -1.0
    0x7f7f_ffff, // the largest finite value
    0x7f80_0000, // +inf
    0xff80_0000, // -inf
    0x7fc0_0000, // the quiet NaN
    0xffc0_0001, // a quiet NaN with its sign set and a payload
    0x7f80_0001, // a signalling NaN
    0xffff_ffff,
];

/// The hard bit patterns of `f64`.
pub const F64: [u64; 12] = [
    0,
    0x8000_0000_0000_0000,
    1,
    0x000f_ffff_ffff_ffff,
    0x3ff0_0000_0000_0000,
    0xbff0_0000_0000_0000,
    0x7fef_ffff_ffff_ffff,
    0x7ff0_0000_0000_0000,
    0xfff0_0000_0000_0000,
    0x7ff8_0000_0000_0000,
    0xfff0_0000_0000_0001,
    0x7ff4_0000_0000_0000,
];

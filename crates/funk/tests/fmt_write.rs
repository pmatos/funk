//! `funk fmt --write` replaces a file all at once, keeps its permissions,
//! and touches nothing else (ADR-2026-10-30-1032).

#![cfg(unix)]

mod common;

use std::fs::{self, Permissions};
use std::os::unix::fs::PermissionsExt;
use std::path::Path;

use common::{SEVEN, dir, funk, text};

fn messy() -> String {
    SEVEN.replace("  ret", "\tret")
}

fn mode(path: &Path) -> u32 {
    fs::symlink_metadata(path).unwrap().permissions().mode() & 0o777
}

/// The names in a directory, sorted.
fn names(dir: &Path) -> Vec<String> {
    let mut names: Vec<String> = fs::read_dir(dir)
        .unwrap()
        .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
        .collect();
    names.sort();
    names
}

/// Whether this process may write `path` despite its permissions, as root
/// may.
fn writes_anyway(path: &Path) -> bool {
    fs::OpenOptions::new().write(true).open(path).is_ok()
}

#[test]
fn fmt_write_keeps_the_file_permissions() {
    let d = dir("write-perms");
    let path = d.join("perms.fir");
    fs::write(&path, messy()).unwrap();
    fs::set_permissions(&path, Permissions::from_mode(0o640)).unwrap();
    let out = funk(&["fmt", "--write", path.to_str().unwrap()], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert_eq!(fs::read_to_string(&path).unwrap(), SEVEN);
    assert_eq!(mode(&path), 0o640);
    assert_eq!(names(&d), ["perms.fir"]);
}

#[test]
fn fmt_write_leaves_files_and_links_at_temporary_names_alone() {
    let d = dir("write-temps");
    let path = d.join("s.fir");
    fs::write(&path, messy()).unwrap();
    let victim = d.join("victim.txt");
    fs::write(&victim, "victim\n").unwrap();
    fs::set_permissions(&victim, Permissions::from_mode(0o600)).unwrap();
    std::os::unix::fs::symlink("victim.txt", d.join(".s.fir.funk-fmt.0.tmp")).unwrap();
    std::os::unix::fs::symlink("victim.txt", d.join("s.fir.funk-fmt.tmp")).unwrap();
    let precious = d.join(".s.fir.funk-fmt.1.tmp");
    fs::write(&precious, "precious\n").unwrap();
    fs::set_permissions(&precious, Permissions::from_mode(0o444)).unwrap();
    let before = names(&d);
    let out = funk(&["fmt", "--write", path.to_str().unwrap()], "");
    assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    assert!(fs::symlink_metadata(&path).unwrap().is_file());
    assert_eq!(fs::read_to_string(&path).unwrap(), SEVEN);
    assert_eq!(fs::read_to_string(&victim).unwrap(), "victim\n");
    assert_eq!(mode(&victim), 0o600);
    assert_eq!(fs::read_to_string(&precious).unwrap(), "precious\n");
    assert_eq!(names(&d), before);
}

#[test]
fn fmt_write_refuses_a_file_it_may_not_write() {
    let d = dir("write-readonly");
    let path = d.join("ro.fir");
    fs::write(&path, messy()).unwrap();
    fs::set_permissions(&path, Permissions::from_mode(0o444)).unwrap();
    if writes_anyway(&path) {
        return;
    }
    let p = path.to_str().unwrap();
    let out = funk(&["fmt", "--write", "--json", p], "");
    assert_eq!(out.status.code(), Some(2));
    let json = text(&out.stdout);
    assert!(
        json.starts_with(&format!(
            r#"{{"file":"{p}","verdict":"io-error","diagnostics":[{{"kind":"io-error","message":"cannot write {p}: "#
        )),
        "{json}"
    );
    assert!(json.ends_with("\"canonical\":false}\n"), "{json}");
    assert_eq!(fs::read_to_string(&path).unwrap(), messy());
    assert_eq!(names(&d), ["ro.fir"]);
}

#[test]
fn fmt_write_in_a_read_only_directory_is_an_io_error() {
    let d = dir("write-rodir");
    let path = d.join("a.fir");
    fs::write(&path, messy()).unwrap();
    fs::set_permissions(&d, Permissions::from_mode(0o555)).unwrap();
    let probe = fs::File::create(d.join("probe"));
    if probe.is_ok() {
        fs::set_permissions(&d, Permissions::from_mode(0o755)).unwrap();
        return;
    }
    let out = funk(&["fmt", "--write", path.to_str().unwrap()], "");
    fs::set_permissions(&d, Permissions::from_mode(0o755)).unwrap();
    assert_eq!(out.status.code(), Some(2));
    let err = text(&out.stderr);
    assert!(err.contains(": error: cannot write "), "{err}");
    assert_eq!(err.lines().count(), 1, "{err}");
    assert_eq!(fs::read_to_string(&path).unwrap(), messy());
}

#[test]
fn concurrent_fmt_write_runs_all_succeed() {
    let d = dir("write-concurrent");
    let path = d.join("big.fir");
    let func = |i: usize| {
        format!("func @f{i}() -> i32 {{\n^e:\n  %c: i32 = const {i} @0\n\tret %c @0\n}}\n\n")
    };
    let mut big: String = (0..3000).map(func).collect();
    big.push_str("locs {\n  @0 = unknown\n}\n");
    fs::write(&path, &big).unwrap();
    let p = path.to_str().unwrap();
    let runs: Vec<_> = (0..6)
        .map(|_| {
            std::process::Command::new(env!("CARGO_BIN_EXE_funk"))
                .args(["fmt", "--write", p])
                .stderr(std::process::Stdio::piped())
                .spawn()
                .unwrap()
        })
        .collect();
    for run in runs {
        let out = run.wait_with_output().unwrap();
        assert_eq!(out.status.code(), Some(0), "{}", text(&out.stderr));
    }
    assert_eq!(
        fs::read_to_string(&path).unwrap(),
        big.replace("\tret", "  ret")
    );
    assert_eq!(names(&d), ["big.fir"]);
}

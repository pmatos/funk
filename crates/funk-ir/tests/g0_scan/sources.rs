//! The sources of `funk-ir` that G0's source check reads: every module of
//! `src/` but the dialects, the module generator and the files of the
//! modules that a source compiles only for its unit tests.

use std::path::{Path, PathBuf};

use super::{TestMod, test_modules, tokens};

/// Whether the module at `rel` defines a dialect's ops or builds core
/// modules for the property tests, so it may name the core dialect's ops.
fn names_ops(rel: &str) -> bool {
    rel.starts_with("src/dialects/") || rel == "src/generate.rs" || rel.starts_with("src/generate/")
}

/// `path`, without its `.` and `..` parts.
fn normal(path: &str) -> String {
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "" | "." => {}
            ".." => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    parts.join("/")
}

/// The files of a test module of the source at `rel`: its file, and the
/// directory, ending in `/`, of the modules that it declares in turn.
pub fn test_module_files(rel: &str, m: &TestMod) -> [String; 2] {
    let (dir, file) = rel.rsplit_once('/').unwrap_or(("", rel));
    let path = match &m.path {
        // A `#[path]` is relative to the directory of the source.
        Some(p) => normal(&format!("{dir}/{p}")),
        None if matches!(file, "lib.rs" | "main.rs" | "mod.rs") => {
            format!("{dir}/{}.rs", m.name)
        }
        None => format!("{dir}/{}/{}.rs", file.trim_end_matches(".rs"), m.name),
    };
    let below = match path.strip_suffix("/mod.rs") {
        Some(d) => format!("{d}/"),
        None => format!("{}/", path.trim_end_matches(".rs")),
    };
    [path, below]
}

/// The Rust files under `dir`, relative to `root`, with their text.
fn rust_files(root: &Path, dir: PathBuf) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let mut dirs = vec![dir];
    while let Some(dir) = dirs.pop() {
        for entry in std::fs::read_dir(&dir).expect("a source directory") {
            let path = entry.expect("a directory entry").path();
            if path.is_dir() {
                dirs.push(path);
            } else if path.extension().is_some_and(|x| x == "rs") {
                let rel = path.strip_prefix(root).expect("under the crate");
                let rel = rel.to_string_lossy().replace('\\', "/");
                out.push((rel, std::fs::read_to_string(&path).expect("a UTF-8 source")));
            }
        }
    }
    out
}

/// The modules of the crate at `root` whose code sees every op alike, with
/// their text: all of `src/` but the dialects, which define ops, the module
/// generator, which builds core modules for the property tests, and the
/// files of each `#[cfg(test)]` module. A new module is checked unless it
/// goes in one of those places.
pub fn generic_sources(root: &Path) -> Vec<(String, String)> {
    let all = rust_files(root, root.join("src"));
    let tests: Vec<String> = all
        .iter()
        .flat_map(|(rel, src)| {
            test_modules(&tokens(src))
                .into_iter()
                .flat_map(|m| test_module_files(rel, &m))
                .collect::<Vec<_>>()
        })
        .collect();
    let is_test = |rel: &str| {
        tests.iter().any(|t| match t.strip_suffix('/') {
            Some(_) => rel.starts_with(t.as_str()),
            None => rel == t,
        })
    };
    let mut out: Vec<(String, String)> = all
        .into_iter()
        .filter(|(rel, _)| !names_ops(rel) && !is_test(rel))
        .collect();
    out.sort();
    out
}

#[test]
fn a_test_modules_files_are_found_as_rustc_finds_them() {
    let m = |name: &str, path: Option<&str>| TestMod {
        name: name.into(),
        path: path.map(String::from),
    };
    assert_eq!(
        test_module_files("src/verify/cfg.rs", &m("more_tests", None)),
        ["src/verify/cfg/more_tests.rs", "src/verify/cfg/more_tests/"]
    );
    assert_eq!(
        test_module_files("src/verify/mod.rs", &m("tests", None)),
        ["src/verify/tests.rs", "src/verify/tests/"]
    );
    assert_eq!(
        test_module_files("src/lib.rs", &m("tests", Some("t.rs"))),
        ["src/t.rs", "src/t/"]
    );
    assert_eq!(
        test_module_files("src/a/b.rs", &m("t", Some("../x/mod.rs"))),
        ["src/x/mod.rs", "src/x/"]
    );
}

#[test]
fn the_files_of_a_test_module_are_not_checked() {
    let root = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join("g0-sources");
    let _ = std::fs::remove_dir_all(&root);
    let files = [
        (
            "src/lib.rs",
            "pub mod verify;\n#[cfg(test)]\n#[path = \"t.rs\"]\nmod t;\n",
        ),
        ("src/t.rs", "const OP: &str = \"add\";\n"),
        ("src/verify/mod.rs", "mod cfg;\n"),
        (
            "src/verify/cfg.rs",
            "#[cfg(test)]\nmod more_tests;\nmod kept;\n",
        ),
        ("src/verify/cfg/kept.rs", ""),
        ("src/verify/cfg/more_tests.rs", "mod deeper;\n"),
        ("src/verify/cfg/more_tests/deeper.rs", ""),
        ("src/dialects/core.rs", ""),
    ];
    for (rel, text) in files {
        let path = root.join(rel);
        std::fs::create_dir_all(path.parent().expect("a parent")).expect("a directory");
        std::fs::write(path, text).expect("a file");
    }
    let found: Vec<String> = generic_sources(&root).into_iter().map(|(r, _)| r).collect();
    assert_eq!(
        found,
        [
            "src/lib.rs",
            "src/verify/cfg.rs",
            "src/verify/cfg/kept.rs",
            "src/verify/mod.rs"
        ]
    );
    std::fs::remove_dir_all(&root).expect("removed");
}

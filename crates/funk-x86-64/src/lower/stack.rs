//! Stack needs from the calls that lowering emitted, not reconstructed fir.
//!
//! A need includes the function's frame, return address and saved `%rbp`,
//! plus its deepest call or runtime helper. Calls inside one cycle do not
//! count; the cycle and every function reaching it are marked recursive.
//! All arithmetic saturates. Tarjan's traversal keeps its path on the heap,
//! so a chain of calls takes no native stack per function.
//!
//! See `docs/decisions/x86-64-backend-executable.md#the-figure`.

/// The stack a run of one function needs.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Need {
    /// The bytes below the caller's return address: the most that any run
    /// uses when the function is not recursive, and otherwise the most that
    /// a run uses when it makes no call within a cycle.
    pub bytes: u64,
    /// Whether a cycle of calls is reachable from the function, so that a
    /// run may need more than `bytes`, as many more as its arguments say.
    pub recursive: bool,
}

/// Emitted stack facts for one function. Call indices address this same
/// module's function order; outgoing bytes exclude the return address.
#[derive(Debug, Default)]
pub(super) struct Function {
    pub frame: i32,
    pub calls: Vec<Call>,
    pub helper_stack: u64,
}

/// One emitted call: its callee's index and peak outgoing argument bytes.
type Call = (usize, u64);

/// Complete stack needs, in function order. Only lowering constructs the
/// facts; this calculation knows nothing about fir types or call placement.
pub(super) fn needs(functions: &[Function]) -> Vec<Need> {
    let mut out = vec![Need::default(); functions.len()];
    let mut component = vec![0; functions.len()];
    // Each component comes after every component that it calls, whose
    // needs are known by then; a call within the component does not count.
    for (c, members) in components(functions).into_iter().enumerate() {
        for &f in &members {
            component[f] = c + 1;
        }
        let cycle = members.len() > 1
            || functions[members[0]]
                .calls
                .iter()
                .any(|&(g, _)| g == members[0]);
        for &f in &members {
            let mut need = Need {
                bytes: functions[f].helper_stack,
                recursive: cycle,
            };
            for &(g, pushed) in &functions[f].calls {
                if component[g] == c + 1 {
                    continue;
                }
                let below = out[g];
                need.bytes = need.bytes.max(pushed.saturating_add(below.bytes));
                need.recursive |= below.recursive;
            }
            let own = u64::from(functions[f].frame.unsigned_abs()) + 16;
            need.bytes = need.bytes.saturating_add(own);
            out[f] = need;
        }
    }
    out
}

/// The strongly connected components of the emitted call graph, by
/// Tarjan's algorithm, each after every component that it calls. A
/// component is one function, or the functions of a cycle of calls.
fn components(functions: &[Function]) -> Vec<Vec<usize>> {
    const UNSEEN: usize = usize::MAX;
    let n = functions.len();
    let (mut order, mut low) = (vec![UNSEEN; n], vec![0; n]);
    let mut on_path = vec![false; n];
    let (mut path, mut out, mut next) = (Vec::new(), Vec::new(), 0);
    for root in 0..n {
        if order[root] != UNSEEN {
            continue;
        }
        // The functions being visited, each with its next call to follow.
        let mut work = vec![(root, 0)];
        (order[root], low[root], next) = (next, next, next + 1);
        path.push(root);
        on_path[root] = true;
        while let Some(top) = work.last_mut() {
            let (f, k) = *top;
            if let Some(&(g, _)) = functions[f].calls.get(k) {
                top.1 += 1;
                if order[g] == UNSEEN {
                    (order[g], low[g], next) = (next, next, next + 1);
                    path.push(g);
                    on_path[g] = true;
                    work.push((g, 0));
                } else if on_path[g] {
                    low[f] = low[f].min(order[g]);
                }
                continue;
            }
            work.pop();
            if let Some(&(caller, _)) = work.last() {
                low[caller] = low[caller].min(low[f]);
            }
            if low[f] == order[f] {
                let mut members = Vec::new();
                while let Some(g) = path.pop() {
                    on_path[g] = false;
                    members.push(g);
                    if g == f {
                        break;
                    }
                }
                out.push(members);
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use funk_ir::{Registry, parse};

    use super::*;

    fn function(frame: i32, calls: &[(usize, u64)], helper_stack: u64) -> Function {
        Function {
            frame,
            calls: calls.to_vec(),
            helper_stack,
        }
    }

    fn need(bytes: u64, recursive: bool) -> Need {
        Need { bytes, recursive }
    }

    fn lowered(text: &str) -> Vec<Need> {
        let m = parse(text, &Registry::core()).unwrap();
        crate::lower::module(&m).unwrap().needs
    }

    #[test]
    fn leaves_and_chains_include_every_frame() {
        assert_eq!(needs(&[]), []);
        assert_eq!(
            needs(&[function(0, &[], 0), function(4096, &[], 0)]),
            [need(16, false), need(4112, false)]
        );
        assert_eq!(
            needs(&[
                function(32, &[(1, 0)], 0),
                function(4096, &[(2, 0)], 0),
                function(48, &[], 0),
            ]),
            [need(4224, false), need(4176, false), need(64, false)]
        );
    }

    #[test]
    fn a_call_includes_its_emitted_outgoing_bytes() {
        for pushed in [0, 16, 32, 48, 4096] {
            assert_eq!(
                needs(&[function(16, &[(1, pushed)], 0), function(16, &[], 0)])[0],
                need(64 + pushed, false)
            );
        }
    }

    #[test]
    fn sequential_calls_and_helpers_take_the_maximum_not_the_sum() {
        assert_eq!(
            needs(&[
                function(0, &[(1, 0), (2, 16), (1, 0)], 24),
                function(1024, &[(3, 0)], 24),
                function(16, &[(3, 0)], 24),
                function(64, &[], 24),
            ]),
            [
                need(1160, false),
                need(1144, false),
                need(136, false),
                need(104, false)
            ]
        );
        assert_eq!(
            needs(&[function(0, &[(1, 0)], 128), function(0, &[], 0)])[0],
            need(144, false)
        );
    }

    #[test]
    fn self_and_mutual_cycles_ignore_internal_calls() {
        assert_eq!(
            needs(&[
                function(32, &[(0, 0), (1, 0), (0, 4096)], 0),
                function(256, &[], 0),
            ]),
            [need(320, true), need(272, false)]
        );
        assert_eq!(
            needs(&[
                function(32, &[(1, 4096)], 0),
                function(48, &[(0, 0), (2, 16)], 0),
                function(16, &[], 0),
            ]),
            [need(48, true), need(112, true), need(32, false)]
        );
    }

    #[test]
    fn recursive_reachability_does_not_affect_disconnected_functions() {
        assert_eq!(
            needs(&[
                function(16, &[(2, 0), (1, 0)], 0),
                function(4096, &[(1, 0)], 0),
                function(0, &[], 0),
                function(0, &[(2, 0)], 0),
            ]),
            [
                need(4144, true),
                need(4112, true),
                need(16, false),
                need(32, false)
            ]
        );
    }

    #[test]
    fn stack_arithmetic_saturates() {
        assert_eq!(
            needs(&[
                function(i32::MIN, &[(1, u64::MAX)], 0),
                function(16, &[], 0),
                function(16, &[], u64::MAX),
            ]),
            [
                need(u64::MAX, false),
                need(32, false),
                need(u64::MAX, false)
            ]
        );
    }

    #[test]
    fn a_long_chain_and_a_long_cycle_are_sized_on_a_small_stack() {
        let n = 100_000;
        let mut functions: Vec<Function> =
            (1..=n).map(|next| function(16, &[(next, 0)], 0)).collect();
        functions.push(function(16, &[], 0));
        let chain = needs(&functions);
        assert_eq!(chain[0], need(32 * (n as u64 + 1), false));
        assert_eq!(chain[n], need(32, false));
        functions[n].calls.push((0, 0));
        assert!(needs(&functions).iter().all(|&x| x == need(32, true)));
    }

    #[test]
    fn emitted_calls_count_register_overflow_and_i128_alignment() {
        for (types, pushed, frame) in [
            ("i64, i64, i64, i64, i64, i64", 0, 48),
            ("i64, i64, i64, i64, i64, i64, i64", 16, 64),
            ("i64, i64, i64, i64, i64, i64, i64, i64", 16, 64),
            ("i64, i64, i64, i64, i64, i64, i64, i64, i64", 32, 80),
            ("i128, i128, i128", 0, 48),
            ("i128, i128, i128, i128", 16, 64),
            ("i64, i64, i64, i64, i64, i128, i64", 16, 64),
            ("i64, i64, i64, i64, i64, i64, i64, i128", 32, 80),
            ("i128, i128, i128, i64, i128, i64, i128", 64, 96),
        ] {
            let types: Vec<&str> = types.split(", ").collect();
            let params = types
                .iter()
                .enumerate()
                .map(|(i, t)| format!("%p{i}: {t}"))
                .collect::<Vec<_>>()
                .join(", ");
            let args = (0..types.len())
                .map(|i| format!("%p{i}"))
                .collect::<Vec<_>>()
                .join(", ");
            let text = format!(
                "func @g({params}) {{\n^entry:\n  ret @0\n}}\n\n\
                 func @f({params}) {{\n^entry:\n  call @g {args} @0\n  ret @0\n}}\n\n\
                 locs {{\n  @0 = unknown\n}}\n"
            );
            assert_eq!(
                lowered(&text)[1],
                need(2 * (16 + frame) + pushed, false),
                "{types:?}"
            );
        }
    }

    #[test]
    fn result_area_addresses_shift_integer_arguments_and_pairs() {
        let params = "%a: i64, %b: i64, %c: i64, %d: i64, %x: i128";
        for (results, values, defs, bytes) in [
            ("i128", "%x", "%r: i128", 160),
            ("i128, i64", "%x, %a", "%r: i128, %s: i64", 224),
            (
                "i64, i128, i1",
                "%a, %x, %t",
                "%r: i64, %s: i128, %u: i1",
                256,
            ),
        ] {
            let text = format!(
                "func @g({params}) -> {results} {{\n^entry:\n  %t: i1 = const true @0\n  \
                 ret {values} @0\n}}\n\n\
                 func @f({params}) {{\n^entry:\n  {defs} = call @g %a, %b, %c, %d, %x @0\n  \
                 ret @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
            );
            assert_eq!(lowered(&text)[1], need(bytes, false), "{results}");
        }
        let params = "%a: i64, %b: i64, %c: i64, %d: i64, %e: i64, %f: i64";
        for (count, pushed, caller_frame) in [
            (0, 0, 48),
            (1, 0, 64),
            (2, 0, 64),
            (3, 16, 112),
            (9, 16, 208),
        ] {
            let results = vec!["i64"; count].join(", ");
            let signature = if count == 0 {
                String::new()
            } else {
                format!(" -> {results}")
            };
            let returned = vec!["%a"; count].join(", ");
            let defs = (0..count)
                .map(|i| format!("%r{i}: i64"))
                .collect::<Vec<_>>()
                .join(", ");
            let defs = if count == 0 {
                String::new()
            } else {
                format!("{defs} = ")
            };
            let text = format!(
                "func @g({params}){signature} {{\n^entry:\n  ret {returned} @0\n}}\n\n\
                 func @f({params}) {{\n^entry:\n  \
                 {defs}call @g %a, %b, %c, %d, %e, %f @0\n  ret @0\n}}\n\n\
                 locs {{\n  @0 = unknown\n}}\n"
            );
            let callee_frame = if count >= 3 { 64 } else { 48 };
            assert_eq!(
                lowered(&text)[1],
                need(16 + caller_frame + pushed + 16 + callee_frame, false)
            );
        }
    }

    #[test]
    fn helper_families_keep_the_global_allowance() {
        assert_eq!(
            lowered(
                "func @d(%a: i128, %b: i128) -> i128 {\n^entry:\n  \
                     %q: i128 = sdiv %a, %b @0\n  ret %q @0\n}\n\n\
                     func @n(%a: i64, %b: i64) -> i64 {\n^entry:\n  \
                     %q: i64 = urem %a, %b @0\n  ret %q @0\n}\n\n\
                     func @c(%a: i128, %b: i128) -> i128 {\n^entry:\n  \
                     %q: i128 = call @d %a, %b @0\n  %r: i128 = urem %q, %b @0\n  \
                     ret %r @0\n}\n\nlocs {\n  @0 = unknown\n}\n"
            ),
            [need(88, false), need(48, false), need(168, false)]
        );
        for (ty, op) in [
            ("f32", "fma round(rne) %a, %b, %c"),
            ("f64", "fma round(rne) %a, %b, %c"),
            ("f32", "frem %a, %b"),
            ("f64", "fmod %a, %b"),
        ] {
            let text = format!(
                "func @f(%a: {ty}, %b: {ty}, %c: {ty}) -> {ty} {{\n^entry:\n  \
                 %r: {ty} = {op} @0\n  ret %r @0\n}}\n\nlocs {{\n  @0 = unknown\n}}\n"
            );
            assert_eq!(lowered(&text), [need(72, false)]);
        }
    }

    #[test]
    fn lowering_resolves_forward_calls_and_the_first_duplicate_symbol() {
        let text = "func @main() {\n^entry:\n  call @leaf @0\n  ret @0\n}\n\n\
                    func @leaf() {\n^entry:\n  ret @0\n}\n\n\
                    func @leaf(%x: i128) {\n^entry:\n  ret @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        assert_eq!(lowered(text)[0], need(32, false));
        let text = "func @leaf() {\n^entry:\n  ret @0\n}\n\n\
                    func @main() {\n^entry:\n  call @leaf @0\n  ret @0\n}\n\n\
                    locs {\n  @0 = unknown\n}\n";
        assert_eq!(lowered(text)[1], need(32, false));
    }

    #[test]
    fn emitted_mixed_calls_keep_their_stack_reservation() {
        let params = (0..6)
            .map(|i| format!("%a{i}: i64"))
            .chain((0..9).map(|i| format!("%x{i}: f64")))
            .chain(["%p: i128".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let args = (0..6)
            .map(|i| format!("%a{i}"))
            .chain((0..9).map(|i| format!("%x{i}")))
            .chain(["%p".into()])
            .collect::<Vec<_>>()
            .join(", ");
        let text = format!(
            "func @g({params}) -> i128, i64 {{\n^entry:\n  ret %p, %a0 @0\n}}\n\n\
             func @f({params}) {{\n^entry:\n  \
             %r: i128, %s: i64 = call @g {args} @0\n  \
             %t: f64 = fma round(rne) %x0, %x1, %x2 @0\n  ret @0\n}}\n\n\
             locs {{\n  @0 = unknown\n}}\n"
        );
        let m = parse(&text, &Registry::core()).unwrap();
        let lowered = crate::lower::module(&m).unwrap();
        assert_eq!(lowered.needs, [need(160, false), need(416, false)]);
    }
}

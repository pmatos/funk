//! The parallel move of a branch's block arguments.
//!
//! A branch passes values to its successor's arguments all at once: `br
//! ^loop(%b, %a)` from `^loop(%a, %b)` swaps them. Each value has a slot of
//! its own (ADR-2026-10-30-1230), so the branch copies slots into slots,
//! and a copy must not overwrite a slot that a later copy still reads.
//! [`sequence`] orders the copies so that none does, and breaks each cycle
//! of them, such as a swap or a rotation, with one scratch register.

/// Where a copy reads its value: a slot, or the scratch register that holds
/// the value a cycle's first slot had.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Src<T> {
    /// A slot.
    At(T),
    /// The scratch register.
    Temp,
}

/// One step of a parallel move done in sequence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Step<T> {
    /// Copy the value at `Src` into the slot.
    Copy(Src<T>, T),
    /// Save the value of the slot in the scratch register.
    Save(T),
}

/// The steps that give each destination of `moves`, a list of
/// `(destination, source)` pairs, the value its source had before the
/// first step. The destinations must be distinct; a source may feed several
/// of them, and a destination may be the source of another pair.
///
/// A pair whose destination is its source needs no step. Then, as long as
/// pairs remain, one whose destination no other pair still reads is
/// copied. When none is left, every remaining destination is read by
/// exactly one remaining pair: the pairs form cycles, and nothing reads the
/// scratch register. The first destination is saved in it, and the pairs
/// that read that slot read the register instead, which opens its cycle.
pub fn sequence<T: Copy + Eq>(moves: &[(T, T)]) -> Vec<Step<T>> {
    debug_assert!(
        moves
            .iter()
            .enumerate()
            .all(|(i, (d, _))| moves[..i].iter().all(|(e, _)| e != d)),
        "the destinations of a parallel move are distinct"
    );
    let mut pending: Vec<(T, Src<T>)> = moves
        .iter()
        .filter(|(d, s)| d != s)
        .map(|&(d, s)| (d, Src::At(s)))
        .collect();
    let mut steps = Vec::with_capacity(pending.len() + 1);
    while !pending.is_empty() {
        let read = |d: T, pending: &[(T, Src<T>)]| pending.iter().any(|(_, s)| *s == Src::At(d));
        match pending.iter().position(|&(d, _)| !read(d, &pending)) {
            Some(i) => {
                let (d, s) = pending.remove(i);
                steps.push(Step::Copy(s, d));
            }
            None => {
                let d = pending[0].0;
                steps.push(Step::Save(d));
                for (_, s) in &mut pending {
                    if *s == Src::At(d) {
                        *s = Src::Temp;
                    }
                }
            }
        }
    }
    steps
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Runs `steps` on slots `0..n` that hold their own numbers, with a
    /// scratch register that holds nothing yet.
    fn run(steps: &[Step<usize>], n: usize) -> Vec<usize> {
        let mut slots: Vec<usize> = (0..n).collect();
        let mut temp = None;
        for step in steps {
            match *step {
                Step::Save(d) => temp = Some(slots[d]),
                Step::Copy(Src::At(s), d) => slots[d] = slots[s],
                Step::Copy(Src::Temp, d) => slots[d] = temp.expect("the register was saved"),
            }
        }
        slots
    }

    /// The slots after `moves` done at once.
    fn at_once(moves: &[(usize, usize)], n: usize) -> Vec<usize> {
        let mut slots: Vec<usize> = (0..n).collect();
        for &(d, s) in moves {
            slots[d] = s;
        }
        slots
    }

    /// The number of cycles among `moves`: chains of copies, each reading
    /// the slot that the next one writes, that come back to where they
    /// started. Found by walking from each slot to the slot it reads.
    fn cycles(moves: &[(usize, usize)], n: usize) -> usize {
        let mut reads = vec![None; n];
        for &(d, s) in moves {
            if d != s {
                reads[d] = Some(s);
            }
        }
        // 0: not walked yet, 1: on the current walk, 2: walked before.
        let mut state = vec![0u8; n];
        let mut count = 0;
        for start in 0..n {
            let (mut at, mut walk) = (Some(start), Vec::new());
            while let Some(v) = at {
                if state[v] != 0 {
                    count += usize::from(state[v] == 1);
                    break;
                }
                state[v] = 1;
                walk.push(v);
                at = reads[v];
            }
            for v in walk {
                state[v] = 2;
            }
        }
        count
    }

    #[test]
    fn only_a_cycle_goes_through_the_register() {
        let swap = sequence(&[(0, 1), (1, 0)]);
        assert_eq!(
            swap,
            [
                Step::Save(0),
                Step::Copy(Src::At(1), 0),
                Step::Copy(Src::Temp, 1)
            ]
        );
        let rotate = sequence(&[(0, 1), (1, 2), (2, 0)]);
        assert_eq!(rotate.len(), 4);
        assert_eq!(run(&rotate, 3), [1, 2, 0]);
        assert_eq!(sequence(&[(0, 0), (1, 1)]), []);
        let fan = sequence(&[(1, 0), (2, 0)]);
        assert_eq!(fan, [Step::Copy(Src::At(0), 1), Step::Copy(Src::At(0), 2)]);
        // Slot 0 feeds 1 and 2, and 2 feeds 0: the copy into 1 goes first,
        // then the swap of 0 and 2 goes through the register.
        let both = sequence(&[(1, 0), (2, 0), (0, 2)]);
        assert_eq!(
            both,
            [
                Step::Copy(Src::At(0), 1),
                Step::Save(2),
                Step::Copy(Src::At(0), 2),
                Step::Copy(Src::Temp, 0)
            ]
        );
        assert_eq!(run(&both, 3), [2, 0, 0]);
        // Two swaps need two saves, and a chain needs none.
        let swaps = [(0, 1), (1, 0), (2, 3), (3, 2)];
        assert_eq!(cycles(&swaps, 4), 2);
        let saves = sequence(&swaps)
            .iter()
            .filter(|s| matches!(s, Step::Save(_)))
            .count();
        assert_eq!(saves, 2);
        assert_eq!(cycles(&[(0, 1), (1, 2)], 3), 0);
        assert_eq!(cycles(&[(1, 0), (2, 0), (0, 2)], 3), 1);
    }

    #[test]
    fn every_parallel_move_is_done_in_sequence() {
        let mut seed = 0x2545_f491_4f6c_dd1d_u64;
        let mut next = move |m: u64| {
            seed ^= seed << 13;
            seed ^= seed >> 7;
            seed ^= seed << 17;
            seed % m
        };
        for _ in 0..20_000 {
            let n = 1 + next(7) as usize;
            let mut dsts: Vec<usize> = (0..n).collect();
            for i in (1..n).rev() {
                dsts.swap(i, next(i as u64 + 1) as usize);
            }
            dsts.truncate(next(n as u64 + 1) as usize);
            let moves: Vec<(usize, usize)> =
                dsts.iter().map(|&d| (d, next(n as u64) as usize)).collect();
            let steps = sequence(&moves);
            assert_eq!(run(&steps, n), at_once(&moves, n), "{moves:?}: {steps:?}");
            let copies = moves.iter().filter(|(d, s)| d != s).count();
            let saves = steps.iter().filter(|s| matches!(s, Step::Save(_))).count();
            assert_eq!(saves, cycles(&moves, n), "{moves:?}: {steps:?}");
            assert_eq!(steps.len(), copies + saves, "{moves:?}");
        }
    }
}

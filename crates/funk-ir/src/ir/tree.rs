//! Trees of any depth, walked and built with explicit stacks
//! (ADR-2026-10-30-1333).
//!
//! fir has no limit on how deeply attributes, regions and items nest (#36),
//! so no code here recurses once per level on the native stack: a text
//! nested ten million levels deep parses, prints, verifies, compares and
//! drops on a thread with a small stack. Every walk over attributes and
//! regions is a [`walk`], which keeps the path from the root in a `Vec` on
//! the heap; every tree that is built level by level is built in a [`Nest`];
//! and [`drop_all`] frees a tree one node at a time. The traits that
//! `#[derive]` would write recursively are written on top of these.

use std::hash::Hasher;

/// A step of a depth-first walk.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Step<N> {
    /// The walk reaches a node, before its children.
    Enter(N),
    /// The walk leaves a node, after its children.
    Leave(N),
}

impl<N> Step<N> {
    /// The node the walk reaches, if it reaches one: the steps of a walk
    /// filtered by this are the nodes in depth-first order.
    pub(crate) fn entered(self) -> Option<N> {
        match self {
            Step::Enter(n) => Some(n),
            Step::Leave(_) => None,
        }
    }
}

/// A reference to a node of a tree, which lists the node's children.
pub(crate) trait Node: Copy {
    /// The node's children, in order.
    type Children: Iterator<Item = Self>;

    /// The node's children, in order.
    fn children(self) -> Self::Children;

    /// Whether the node has no children, so that a walk need not keep it
    /// on its path: a walk of a single leaf allocates nothing.
    fn is_leaf(self) -> bool {
        false
    }
}

/// The steps of a depth-first walk of the tree under `root`, children in
/// order.
pub(crate) fn walk<N: Node>(root: N) -> Walk<N> {
    Walk {
        root: Some(root),
        leaf: None,
        path: Vec::new(),
    }
}

/// A depth-first walk: the nodes from the root to the current one, each with
/// the children it has left.
pub(crate) struct Walk<N: Node> {
    root: Option<N>,
    /// A leaf just entered, which the walk leaves next.
    leaf: Option<N>,
    path: Vec<(N, N::Children)>,
}

impl<N: Node> Iterator for Walk<N> {
    type Item = Step<N>;

    fn next(&mut self) -> Option<Step<N>> {
        if let Some(leaf) = self.leaf.take() {
            return Some(Step::Leave(leaf));
        }
        let node = match self.root.take() {
            Some(root) => root,
            None => {
                let (parent, children) = self.path.last_mut()?;
                match children.next() {
                    Some(child) => child,
                    None => {
                        let parent = *parent;
                        self.path.pop();
                        return Some(Step::Leave(parent));
                    }
                }
            }
        };
        if node.is_leaf() {
            self.leaf = Some(node);
        } else {
            self.path.push((node, node.children()));
        }
        Some(Step::Enter(node))
    }
}

/// Whether two trees have the same shape, with nodes at the same places for
/// which `same` holds.
pub(crate) fn equal<N: Node>(a: N, b: N, mut same: impl FnMut(N, N) -> bool) -> bool {
    let (mut a, mut b) = (walk(a), walk(b));
    loop {
        match (a.next(), b.next()) {
            (None, None) => return true,
            (Some(Step::Enter(x)), Some(Step::Enter(y))) if same(x, y) => {}
            (Some(Step::Leave(_)), Some(Step::Leave(_))) => {}
            _ => return false,
        }
    }
}

/// Hashes a tree: its shape, and each node's own parts by `own`. Trees that
/// [`equal`] finds equal hash the same when `own` hashes what `same` compares.
pub(crate) fn hash<N: Node, H: Hasher>(root: N, state: &mut H, mut own: impl FnMut(N, &mut H)) {
    for step in walk(root) {
        match step {
            Step::Enter(n) => {
                state.write_u8(1);
                own(n, state);
            }
            Step::Leave(_) => state.write_u8(0),
        }
    }
}

/// A list being built whose elements own lists of the same kind, nested to
/// any depth, as an op's regions hold blocks of ops. The lists that enclose
/// the one being built wait on a stack, and the last element of each owns
/// the list above it, so each element goes straight to its place.
pub(crate) struct Nest<T> {
    outer: Vec<Vec<T>>,
    list: Vec<T>,
}

impl<T> Nest<T> {
    /// An empty outermost list, with room for `capacity` elements.
    pub(crate) fn new(capacity: usize) -> Nest<T> {
        Nest {
            outer: Vec::new(),
            list: Vec::with_capacity(capacity),
        }
    }

    /// Adds an element to the list being built.
    pub(crate) fn push(&mut self, x: T) {
        self.list.push(x);
    }

    /// The last element of the list being built.
    pub(crate) fn last_mut(&mut self) -> Option<&mut T> {
        self.list.last_mut()
    }

    /// Whether the list being built is empty.
    pub(crate) fn is_empty(&self) -> bool {
        self.list.is_empty()
    }

    /// Whether the list being built is the outermost one.
    pub(crate) fn is_outermost(&self) -> bool {
        self.outer.is_empty()
    }

    /// Starts a list for the last element of the list being built, with
    /// room for `capacity` elements.
    pub(crate) fn open(&mut self, capacity: usize) {
        let inner = Vec::with_capacity(capacity);
        self.outer.push(std::mem::replace(&mut self.list, inner));
    }

    /// Ends the list being built, and returns it with its owner, the last
    /// element of the enclosing list; `None` when it is the outermost one.
    pub(crate) fn close(&mut self) -> Option<(Vec<T>, &mut T)> {
        let outer = self.outer.pop()?;
        let inner = std::mem::replace(&mut self.list, outer);
        let owner = self.list.last_mut().expect("a list opens for an element");
        Some((inner, owner))
    }

    /// The outermost list, once every inner one is closed.
    pub(crate) fn finish(self) -> Vec<T> {
        debug_assert!(self.outer.is_empty(), "every inner list is closed");
        self.list
    }
}

/// Drops `nodes` and every node they own, one at a time: `detach` moves a
/// node's children onto the stack, so that the node drops without them.
pub(crate) fn drop_all<T>(mut nodes: Vec<T>, mut detach: impl FnMut(&mut T, &mut Vec<T>)) {
    while let Some(mut node) = nodes.pop() {
        detach(&mut node, &mut nodes);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A tree of numbers: node `n` has the children `ns[n]`.
    #[derive(Clone, Copy)]
    struct Num<'a>(usize, &'a [Vec<usize>]);

    impl<'a> Node for Num<'a> {
        type Children = std::iter::Map<
            std::iter::Zip<std::slice::Iter<'a, usize>, std::iter::Repeat<&'a [Vec<usize>]>>,
            fn((&'a usize, &'a [Vec<usize>])) -> Num<'a>,
        >;

        fn children(self) -> Self::Children {
            self.1[self.0]
                .iter()
                .zip(std::iter::repeat(self.1))
                .map(|(&n, ns)| Num(n, ns))
        }
    }

    fn steps(ns: &[Vec<usize>]) -> String {
        walk(Num(0, ns))
            .map(|s| match s {
                Step::Enter(n) => format!("<{}", n.0),
                Step::Leave(n) => format!("{}>", n.0),
            })
            .collect()
    }

    #[test]
    fn a_walk_visits_children_in_order_depth_first() {
        let ns = [vec![1, 3], vec![2], vec![], vec![]];
        assert_eq!(steps(&ns), "<0<1<22>1><33>0>");
        let same = |a: Num<'_>, b: Num<'_>| a.0 == b.0;
        assert!(equal(Num(0, &ns), Num(0, &ns), same));
        let other = [vec![1, 3], vec![], vec![], vec![]];
        assert!(!equal(Num(0, &ns), Num(0, &other), same));
    }

    #[test]
    fn a_nest_puts_each_list_under_its_owner() {
        #[derive(Debug, PartialEq)]
        struct T(u8, Vec<T>);
        let mut nest = Nest::new(1);
        nest.push(T(1, Vec::new()));
        nest.open(1);
        nest.push(T(2, Vec::new()));
        nest.push(T(3, Vec::new()));
        let (inner, owner) = nest.close().expect("an inner list");
        owner.1 = inner;
        assert!(nest.is_outermost() && nest.close().is_none());
        let built = nest.finish();
        assert_eq!(built, vec![T(1, vec![T(2, vec![]), T(3, vec![])])]);
    }
}

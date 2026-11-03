import FirTest.Validate

/-!
Tests of `fir-ref`'s dominator tree (#55). On graphs, its answers are the
spec's search's, `dominatesIn`, for every pair of labels: on graphs chosen
for the cases the lifting must handle, and on 300 graphs drawn at random.
On functions, the check runs `FirRef.problemsIn` (this module imports
`FirRef.Fast` through `FirTest.Validate`) and finds the problems of
dominance; on chains of 100,000 blocks, it accepts a function where each
block uses the value of the block before it, and one where each uses the
value of the entry. The last checks pin the axioms of the theorems.
-/

namespace FirTest.Dominators

open Fir Fir.Core FirRef

/-- The graph of the nodes `nodes` and the edges `edges`. -/
def graphOf (nodes : List Name) (edges : List (Name × Name)) : Graph :=
  Std.HashMap.ofList (nodes.map fun x => (x, (edges.filter (·.1 == x)).map (·.2)))

/-- The tree from the entry `e` and the spec's search agree on whether `a`
dominates `l`, for every pair of `labels`. -/
def agrees (g : Graph) (e : Name) (labels : List Name) : Bool :=
  labels.all fun a => labels.all fun l =>
    dominatesBy (dominance g (some e)) a l == dominatesIn g [e] a l

/-- The pairs of distinct `labels` where the first dominates the second, by
the tree from the entry `e`. -/
def dominated (g : Graph) (e : Name) (labels : List Name) : List (Name × Name) :=
  labels.flatMap fun a =>
    (labels.filter fun l => a != l && dominatesBy (dominance g (some e)) a l).map (a, ·)

/-! # Graphs -/

/-- A diamond: the entry branches to `a` and `b`, which join at `c`. -/
def diamond : Graph := graphOf ["e", "a", "b", "c"] [("e", "a"), ("e", "b"), ("a", "c"), ("b", "c")]

#guard agrees diamond "e" ["e", "a", "b", "c", "zz"]
#guard dominated diamond "e" ["e", "a", "b", "c"] == [("e", "a"), ("e", "b"), ("e", "c")]

/-- `b` and `c` reach each other, and `x` dominates both: a tree where they
hang from the entry also has each parent an ancestor of each predecessor,
so only lifting from the search's tree finds `x`. -/
def crossed : Graph :=
  graphOf ["s", "x", "b", "c"] [("s", "x"), ("x", "b"), ("x", "c"), ("b", "c"), ("c", "b")]

#guard agrees crossed "s" ["s", "x", "b", "c"]
#guard dominated crossed "s" ["s", "x", "b", "c"] ==
  [("s", "x"), ("s", "b"), ("s", "c"), ("x", "b"), ("x", "c")]

/-- A loop entered from the entry and from `a`: the search reaches `c` from
`b`, and `b` moves to the entry only in the second pass, after `c` has. -/
def twoPasses : Graph :=
  graphOf ["s", "a", "b", "c"] [("s", "a"), ("a", "b"), ("b", "c"), ("c", "b"), ("s", "c")]

#guard agrees twoPasses "s" ["s", "a", "b", "c"]
#guard dominated twoPasses "s" ["s", "a", "b", "c"] == [("s", "a"), ("s", "b"), ("s", "c")]

/-- An irreducible loop, nested loops, a self-loop, a successor that is not
a block, and a block that the entry does not reach. -/
def tangle : Graph :=
  graphOf ["e", "h1", "h2", "b", "x", "a", "b2", "exit", "u"]
    [("e", "h1"), ("h1", "h2"), ("h2", "b"), ("b", "h2"), ("h2", "x"), ("x", "h1"),
     ("h1", "a"), ("h1", "b2"), ("a", "b2"), ("b2", "a"), ("a", "a"), ("a", "exit"),
     ("b2", "out"), ("u", "a")]

#guard agrees tangle "e" ["e", "h1", "h2", "b", "x", "a", "b2", "exit", "u", "out", "zz"]
#guard dominated tangle "e" ["h1", "h2", "b", "x", "a", "b2", "exit"] ==
  [("h1", "h2"), ("h1", "b"), ("h1", "x"), ("h1", "a"), ("h1", "b2"), ("h1", "exit"),
   ("h2", "b"), ("h2", "x"), ("a", "exit")]

-- With no entry, or an entry that is not a block, every block dominates
-- every block, as the spec's search finds.
#guard dominatesBy (dominance diamond none) "a" "c" && dominatesIn diamond [] "a" "c"
#guard agrees diamond "zz" ["e", "a", "b", "c", "zz"]

/-- The next state of a linear congruential generator. -/
def lcg (s : Nat) : Nat := (s * 1103515245 + 12345) % 2147483648

/-- The edges of a random graph over the nodes `n0` to `n(n-1)`, each pair
an edge with probability about 1/3, from the state `s`. Some edges go to
`n(n)`, which is not a node. -/
def randomEdges (n s : Nat) : List (Name × Name) × Nat :=
  (List.range (n * (n + 1))).foldl (fun (es, s) k =>
    let s := lcg s
    if s / 65536 % 3 == 0 then ((s!"n{k / (n + 1)}", s!"n{k % (n + 1)}") :: es, s)
    else (es, s)) ([], s)

/-- The tree and the spec's search agree on `count` random graphs of 2 to 8
nodes. -/
def randomAgree (count : Nat) : Bool :=
  ((List.range count).foldl (fun (ok, s) i =>
    let n := 2 + i % 7
    let (es, s) := randomEdges n s
    let nodes := (List.range n).map (s!"n{·}")
    (ok && agrees (graphOf nodes es) "n0" (s!"n{n}" :: "zz" :: nodes), s)) (true, 1)).1

#guard randomAgree 300

/-! # Functions -/

/-- A block `^b{i}` that defines `%v{i}` from the value `x` and ends with
`term`. -/
def link (i : Nat) (x : Name) (term : Operation CoreDialect) : Block CoreDialect :=
  ⟨s!"b{i}", [], [op [(s!"v{i}", .int 32)] (.freeze 32) [x], term]⟩

/-- A function of `n` blocks in a chain; block `i` uses the value `use i`. -/
def chain (n : Nat) (use : Nat → Name) : Module CoreDialect :=
  moduleOf [⟨"f", [("p", .int 32)], [], ⟨(List.range n).map fun i =>
    link i (use i)
      (if i + 1 = n then op [] (.ret []) [] else op [] .br [] 0 [⟨s!"b{i + 1}", []⟩])⟩⟩]

/-- Block `i` uses the value of block `i - 1`; the entry uses the parameter. -/
def previous (i : Nat) : Name := if i = 0 then "p" else s!"v{i - 1}"

#guard messages (chain 100000 previous) == []
#guard messages (chain 100000 fun i => if i = 0 then "p" else "v0") == []
#guard messages (chain 4 fun i => if i = 1 then "v3" else previous i) ==
  ["%v3 is defined in ^b3, which does not dominate ^b1"]

/-- A diamond whose join uses a value of one arm, and a loop whose header
uses a value of its body. -/
def joins : String := oneFunc ("func @f(%c: i1) {\n^entry:\n  cond_br %c, ^a, ^b @0\n" ++
  "^a:\n  %x: i1 = freeze %c @0\n  br ^j @0\n^b:\n  br ^j @0\n" ++
  "^j:\n  %y: i1 = freeze %x @0\n  br ^h @0\n" ++
  "^h:\n  %z: i1 = freeze %w @0\n  cond_br %c, ^l, ^out @0\n" ++
  "^l:\n  %w: i1 = freeze %y @0\n  br ^h @0\n^out:\n  ret @0\n}\n")

#guard checks joins
  ["%x is defined in ^a, which does not dominate ^j",
   "%w is defined in ^l, which does not dominate ^h"]

/-! # The axioms of the proofs -/

/--
info: 'FirRef.problemsIn_eq_problemsIn' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.problemsIn_eq_problemsIn

/--
info: 'FirRef.dominance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.dominance_eq

end FirTest.Dominators

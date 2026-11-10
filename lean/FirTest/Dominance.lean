import FirTest.Validate

/-!
Tests of `fir-ref`'s dominator tree (#55). On graphs, its answers are the
spec's search's, `dominatesIn`, for every pair of labels: on graphs chosen
for the cases the lifting must handle, on the shapes where lifting alone
takes quadratic time, and on 330 graphs drawn at random. On all of them,
and on 400 more random graphs, the placement by semidominators is the
dominator tree at once (`placesAll`), so the lifting is never needed. On
functions, the check runs `FirRef.problemsIn` (this module imports
`FirRef.Fast` through `FirTest.Validate`) and finds the problems of
dominance; it accepts functions of 100,000 blocks in a chain and of 20,000
blocks in those shapes, each block using a value of a block that dominates
it. The last checks pin the axioms of the theorems.
-/

namespace FirTest.Dominators

open Fir Fir.Core FirRef FirRef.Dom

/-- The graph of the nodes `nodes` and the edges `edges`. -/
def graphOf (nodes : List Name) (edges : List (Name × Name)) : Graph :=
  Std.HashMap.ofList (nodes.map fun x => (x, (edges.filter (·.1 == x)).map (·.2)))

/-- The tree from the entry `e` and the spec's search agree on whether `a`
dominates `l`, for every pair of `labels`. -/
def agrees (g : Graph) (e : Name) (labels : List Name) : Bool :=
  labels.all fun a => labels.all fun l =>
    dominatesBy (dominance g (some e)) a l == dominatesIn g [e] a l

/-- Whether the placement by semidominators passes the check that
`Oracle.build` makes, so that the build needs no lifting. -/
def placesAll (g : Graph) (e : Name) : Bool :=
  !g.contains e ||
    let t := tree g e
    let order := t.order.reverse
    let P := preds g order
    let st := t.placing P e order
    fixed t.num P e st.pm st.js.jump order

/-- The tree agrees with the spec's search on every pair of the graph's
blocks and a label that is not one, and needs no lifting. -/
def sound (g : Graph) (e : Name) : Bool := agrees g e ("zz" :: g.keys) && placesAll g e

/-- The pairs of distinct `labels` where the first dominates the second, by
the tree from the entry `e`. -/
def dominated (g : Graph) (e : Name) (labels : List Name) : List (Name × Name) :=
  labels.flatMap fun a =>
    (labels.filter fun l => a != l && dominatesBy (dominance g (some e)) a l).map (a, ·)

/-! # Graphs -/

/-- A diamond: the entry branches to `a` and `b`, which join at `c`. -/
def diamond : Graph := graphOf ["e", "a", "b", "c"] [("e", "a"), ("e", "b"), ("a", "c"), ("b", "c")]

#guard agrees diamond "e" ["e", "a", "b", "c", "zz"] && placesAll diamond "e"
#guard dominated diamond "e" ["e", "a", "b", "c"] == [("e", "a"), ("e", "b"), ("e", "c")]

/-- `b` and `c` reach each other, and `x` dominates both: a tree where they
hang from the entry also has each parent an ancestor of each predecessor,
so only lifting from the search's tree finds `x`. -/
def crossed : Graph :=
  graphOf ["s", "x", "b", "c"] [("s", "x"), ("x", "b"), ("x", "c"), ("b", "c"), ("c", "b")]

#guard agrees crossed "s" ["s", "x", "b", "c"] && placesAll crossed "s"
#guard dominated crossed "s" ["s", "x", "b", "c"] ==
  [("s", "x"), ("s", "b"), ("s", "c"), ("x", "b"), ("x", "c")]

/-- A loop entered from the entry and from `a`: the search reaches `c` from
`b`, and `b` moves to the entry only in the second pass, after `c` has. -/
def twoPasses : Graph :=
  graphOf ["s", "a", "b", "c"] [("s", "a"), ("a", "b"), ("b", "c"), ("c", "b"), ("s", "c")]

#guard agrees twoPasses "s" ["s", "a", "b", "c"] && placesAll twoPasses "s"
#guard dominated twoPasses "s" ["s", "a", "b", "c"] == [("s", "a"), ("s", "b"), ("s", "c")]

/-- An irreducible loop, nested loops, a self-loop, a successor that is not
a block, and a block that the entry does not reach. -/
def tangle : Graph :=
  graphOf ["e", "h1", "h2", "b", "x", "a", "b2", "exit", "u"]
    [("e", "h1"), ("h1", "h2"), ("h2", "b"), ("b", "h2"), ("h2", "x"), ("x", "h1"),
     ("h1", "a"), ("h1", "b2"), ("a", "b2"), ("b2", "a"), ("a", "a"), ("a", "exit"),
     ("b2", "out"), ("u", "a")]

#guard agrees tangle "e" ["e", "h1", "h2", "b", "x", "a", "b2", "exit", "u", "out", "zz"] &&
  placesAll tangle "e"
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
    (ok && agrees (graphOf nodes es) "n0" (s!"n{n}" :: "zz" :: nodes) &&
      placesAll (graphOf nodes es) "n0", s)) (true, 1)).1

#guard randomAgree 300

/-- The edges of a sparse random graph over the nodes `n0` to `n(n-1)`: each
node has one to three successors, drawn from the nodes and `n(n)`, which is
not one, from the state `s`. -/
def sparseEdges (n s : Nat) : List (Name × Name) × Nat :=
  (List.range n).foldl (fun (es, s) i =>
    let s := lcg s
    (List.range (1 + s / 65536 % 3)).foldl (fun (es, s) _ =>
      let s := lcg s
      ((s!"n{i}", s!"n{s / 65536 % (n + 1)}") :: es, s)) (es, s)) ([], s)

/-- `count` sparse random graphs of `low` nodes and up to `span - 1` more, each
of which passes `ok` from the entry `n0`. -/
def sparseAll (count low span : Nat) (ok : Graph → Name → Bool) : Bool :=
  ((List.range count).foldl (fun (all, s) i =>
    let n := low + i % span
    let (es, s) := sparseEdges n s
    (all && ok (graphOf ((List.range n).map (s!"n{·}")) es) "n0", s)) (true, 7)).1

-- The tree agrees with the spec's search on 30 graphs of 10 to 20 nodes;
-- the placement needs no lifting on 400 graphs of 10 to 209 nodes.
#guard sparseAll 30 10 11 sound
#guard sparseAll 400 10 200 placesAll

/-! # Shapes where lifting alone takes quadratic time -/

/-- The blocks and edges of a function: each block with its successors. -/
abbrev Shape := List (Name × List Name)

/-- The graph of a shape. -/
def Shape.graph (sh : Shape) : Graph :=
  graphOf (sh.map (·.1)) (sh.flatMap fun (l, ss) => ss.map (l, ·))

/-- The entry, a chain of `n` checks that may each leave for one shared exit
`^j` (the "goto fail" shape), and the exit. -/
def exits (n : Nat) : Shape :=
  ("e", ["c1"]) :: (List.range n).map (fun i =>
    (s!"c{i + 1}", [if i + 1 = n then "j" else s!"c{i + 2}", "j"])) ++ [("j", [])]

/-- Loops nested `d` deep: the headers `h1` to `hd` in a chain, and the
latches `td` to `t1`, each of which jumps back to its header or on to the
next latch. -/
def nested (d : Nat) : Shape :=
  ("e", ["h1"]) :: (List.range d).map (fun i =>
    (s!"h{i + 1}", [if i + 1 = d then s!"t{d}" else s!"h{i + 2}"])) ++
  (List.range d).reverse.map (fun i => (s!"t{i + 1}", [s!"h{i + 1}", s!"t{i}"])) ++ [("t0", [])]

/-- Blocks `x1` to `xm` that each reach both neighbours, entered at both
ends: from the entry at `x1`, and through `y` at `xm`. -/
def passes (m : Nat) : Shape :=
  ("e", ["x1", "y"]) :: ("y", [s!"x{m}"]) :: (List.range m).map (fun i =>
    (s!"x{i + 1}", (if i + 1 < m then [s!"x{i + 2}"] else ["z"]) ++
      (if i = 0 then [] else [s!"x{i}"]))) ++ [("z", [])]

/-- Blocks `b0` to `bn` in a chain, where each block past the middle also
jumps back to its mirror image below the middle. -/
def zigzag (n : Nat) : Shape :=
  (List.range n).map (fun i =>
    (s!"b{i}", s!"b{i + 1}" :: if 2 * i > n then [s!"b{n - i}"] else [])) ++ [(s!"b{n}", [])]

#guard sound (exits 40).graph "e" && sound (nested 20).graph "e" &&
  sound (passes 40).graph "e" && sound (zigzag 41).graph "b0" && sound (zigzag 40).graph "b0"

/-! # Functions -/

/-- A block `^b{i}` that defines `%v{i}` from the value `x` and ends with
`term`. -/
def link (i : Nat) (x : Name) (term : Operation CoreDialect) : Block CoreDialect :=
  ⟨s!"b{i}", [], [op [(s!"v{i}", .int 32)] (.freeze 32) [x], term]⟩

/-- A function of `n` blocks in a chain; block `i` uses the value `use i`. -/
def chain (n : Nat) (use : Nat → Name) : Module CoreDialect :=
  moduleOf [⟨"f", [("p", .int 32)], [], ⟨none, (List.range n).map fun i =>
    link i (use i)
      (if i + 1 = n then op [] (.ret []) [] else op [] .br [] 0 [⟨s!"b{i + 1}", []⟩])⟩⟩]

/-- Block `i` uses the value of block `i - 1`; the entry uses the parameter. -/
def previous (i : Nat) : Name := if i = 0 then "p" else s!"v{i - 1}"

#guard messages (chain 100000 previous) == []
#guard messages (chain 100000 fun i => if i = 0 then "p" else "v0") == []
#guard messages (chain 4 fun i => if i = 1 then "v3" else previous i) ==
  ["%v3 is defined in ^b3, which does not dominate ^b1"]

/-- A function of the shape `sh`, with parameters `%p: i32` and `%c: i1`.
Block `l` defines `%vl`, a `freeze` of the value of the block `use l`, or
of `%p` for the entry, and ends with `ret`, `br` or `cond_br %c` by its
number of successors. -/
def ofShape (sh : Shape) (use : Name → Name) : Module CoreDialect :=
  moduleOf [⟨"f", [("p", .int 32), ("c", .int 1)], [], ⟨none, sh.zipIdx.map fun ((l, ss), i) =>
    ⟨l, [], [op [(s!"v{l}", .int 32)] (.freeze 32) [if i = 0 then "p" else s!"v{use l}"],
      match ss with
      | [] => op [] (.ret []) []
      | [s] => op [] .br [] 0 [⟨s, []⟩]
      | ss => op [] .condBr ["c"] 0 (ss.map (⟨·, []⟩))]⟩⟩⟩]

/-- The label of `l`'s letter and the next number, or the number before. -/
def shift (l : Name) (next : Bool) : Name :=
  match l.toList with
  | c :: ds => match (String.ofList ds).toNat? with
    | some k => String.ofList [c] ++ toString (if next then k + 1 else k - 1)
    | none => l
  | [] => l

-- Each check uses the value of the check before it; the exit, the entry's.
#guard messages (ofShape (exits 20000) fun l =>
  if l = "j" ∨ l = "c1" then "e" else shift l false) == []
-- Each block uses the value of its immediate dominator: the header before
-- it, the latch after it, or for `t_d` the header `h_d`.
#guard messages (ofShape (nested 10000) fun l =>
  if l = "h1" then "e" else if l = "t10000" then "h10000"
  else shift l (l.toList.head? == some 't')) == []
-- Each `x` and `y` uses the entry's value, and `z` that of `x_m`.
#guard messages (ofShape (passes 20000) fun l => if l = "z" then "x20000" else "e") == []
-- Each block uses the value of the block before it.
#guard messages (ofShape (zigzag 20000) (shift · false)) == []

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
info: 'FirRef.Dom.dominance_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms FirRef.Dom.dominance_eq

end FirTest.Dominators

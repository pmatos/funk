import Fir.Core.Validation
import Fir.Validation.Rules

/-!
# A function that validation rejects

The rules are propositions, so a check that validation rejects a function is
a theorem. The function below has a block, `^dead`, that no branch reaches.
Its every op is well typed and its every use is dominated, as LLVM would
accept, but it is not valid fir: every block must be reachable from the
entry (ADR-2026-10-30-0817). In text:

```
func @f() -> i32 {
^entry:
  %c: i32 = const 0 @0
  ret %c @0
^dead:
  %d: i32 = const 1 @0
  ret %d @0
}
```

The decidable check behind `fir-ref validate` (#10), and `funk verify` (#9),
must reject it too, with the reason that `^dead` is unreachable.
-/

namespace Fir.Core.Rejects

/-- A function with a block that the entry does not reach. -/
def deadBlock : Func CoreDialect where
  name := "f"
  params := []
  results := [.int 32]
  body := ⟨[
    ⟨"entry", [], [op [("c", .int 32)] (.const 32 0) [], op [] (.ret [.int 32]) ["c"]]⟩,
    ⟨"dead", [], [op [("d", .int 32)] (.const 32 1) [], op [] (.ret [.int 32]) ["d"]]⟩]⟩

/-- Only the entry of `deadBlock` is reachable: no block has a successor. -/
theorem deadBlock_reachable {l : Name} (h : deadBlock.Reachable l) : l = "entry" := by
  induction h with
  | entry he =>
    simp [Func.entryLabel?, Func.blocks, deadBlock] at he
    exact he.symm
  | step _ he _ =>
    obtain ⟨b, hb, _, hl⟩ := he
    simp [Func.blocks, deadBlock] at hb
    rcases hb with rfl | rfl <;> simp [Block.succLabels, op] at hl

/-- Validation rejects `deadBlock`, in any module. -/
theorem deadBlock_rejected (ctx : ModuleContext CoreDialect) : ¬ deadBlock.Valid ctx := by
  intro h
  have hr := h.reachable
  simp [Func.blocks, deadBlock] at hr
  exact absurd (deadBlock_reachable hr.2) (by decide)

end Fir.Core.Rejects

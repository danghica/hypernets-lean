import Hypernets.Copying.PermutedFilling

/-! Reversing an original BPerm specimen by constructing a new common context.
The directed raw pair is never assumed symmetric. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph

structure Reversal {d I O} {G H : Hypernet d I O} (w : FillingWitness template G H) where
  components : ∀ e, FillingWitness template (w.right e) (w.left e)

namespace Reversal
variable {d I O} {G H : Hypernet d I O} {w : FillingWitness template G H} (r : Reversal w)

def witness : FillingWitness template H G :=
  (FillingWitness.expand w.context r.components).congr w.rightIso w.leftIso

/-- The new common context preserves both actual token coordinates. -/
def pointed (v : w.context.Vertex) :
    PointedFilling H (w.rightPosition (.search,v)).2 G (w.leftPosition (.search,v)).2 where
  filling := r.witness
  point := Net.Expansion.host w.context (fun e => (r.components e).context) v
  left := by cases v <;> rfl
  right := by cases v <;> rfl
end Reversal

/-- Recursion descends only into original box bodies. Shallow reversal is
realised by a genuine permuted context; retained corollas remain retained. -/
noncomputable def reverseFilling {d I O} {G H : Hypernet d I O}
    (w : FillingWitness template G H) : Reversal w := by
  have rightFree : ∀ e, FocusFree (w.right e) :=
    fun e x => (w.paired.focusFree w.free).2 ⟨e,x⟩
  refine ⟨fun e => ?_⟩
  apply Classical.choice
  cases w.edges e with
  | retained l r => exact ⟨FillingWitness.of_copies r l (rightFree e)⟩
  | filled h label rel => exact ⟨rel.1.reverseWitness rel.2⟩
  | boxed b label inner l r =>
    have bodyFree : FocusFree b.body := by
      have free := w.free e
      rw [label] at free
      exact free
    let body := FillingWitness.ofDeepFilling bodyFree inner (DeepIso.refl _) (DeepIso.refl _)
    exact ⟨(reverseFilling body).witness.boxedCopies r l⟩
termination_by d

/-- Every pointed residual has an actual reversed filling and exchanged tokens. -/
noncomputable def PointedFilling.symm {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedFilling G v H w) : PointedFilling H w G v := by
  have result := (reverseFilling p.filling).pointed p.point
  rw [p.left,p.right] at result
  exact result
end Hypernets.Copying.BoxPermutation

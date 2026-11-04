import Hypernets.Copying.CommonContextTransfer
import Hypernets.Copying.CopyingDoubleSearch
import Hypernets.Copying.CompleteMatchExecution

/-! Every literal local transition, including all intermediate token modes,
lifts at its actual component coordinate in the computed common complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Combined
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A C)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

noncomputable def afterState (s : State d J K) : State d I O :=
  ⟨afterGraph C f F s.1,(s.2.1,afterPort C f F s.1 s.2.2)⟩

theorem after_step {s t : State d J K} (step : Step s t) :
    Step (afterState C f F s) (afterState C f F t) := by
  cases step with
  | search G h =>
    apply Step.search
    exact Search.expand_insert (frame C f) (afterFamily C f F G) none
      (Search.step_reboundary (CompleteMatchCut.hole_input _ _).symm
        (CompleteMatchCut.hole_output _ _).symm h)
  | rewrite h =>
    exact .rewrite (.expand (frame C f) (afterFamily C f F _) (afterFamily C f F _) none
      (by intro e ne; cases e with | none => exact False.elim (ne rfl) | some e => rfl)
      (rewrite_reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm h))

/-- The full finite run keeps its exact transition count, not merely its
termination result, when all untouched components are restored. -/
theorem after_run {s t : State d J K} {n} (steps : (machine d J K).Steps n s t) :
    (machine d I O).Steps n (afterState C f F s) (afterState C f F t) := by
  induction steps with
  | zero => exact .zero _
  | cons step rest ih => exact .cons (after_step C f F step) ih

/-- Inserting the actual local resume point preserves its wire type. -/
theorem after_label (G : Hypernet d J K) (v : G.Vertex) :
    (afterGraph C f F G).vertexLabel (afterPort C f F G v) = G.vertexLabel v := by
  have labels := Net.Expansion.insert_label (frame C f) (afterFamily C f F G) none
    (Port.cast (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm v)
  refine labels.trans ?_
  have castLabels {U V : List Wire} (hi : J=U) (ho : K=V) (p : G.Vertex) :
      (G.reboundary hi ho).vertexLabel (Port.cast hi ho p) = G.vertexLabel p := by
    cases hi; cases ho; cases p <;> rfl
  exact castLabels _ _ v

end Hypernets.Copying.CommonContextCut

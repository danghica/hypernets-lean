import Hypernets.Copying.ParametricityReadTail
import Hypernets.Copying.CopyingSelectedInput
import Hypernets.Copying.BoxPullWeakeningReverseLambda

/-! Rematch the private read's whole canonical D1,2, including its weakening.
The actual original copying rule at input one gives a literal full-tree
endpoint, proved coherent with the earlier minimal-spine implementation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail.FullCopy
open Graph Combined Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

/-- The read reduct contains the complete original three-edge term distributor. -/
def distributor : Occurrence (CanonicalTree.atDepth .term 2 d) (Dereference.after T d) where
  ports := Net.Expansion.insert (Dereference.afterFrame h) (Dereference.afterFill T) .share
  internals v := .inr ⟨.share,v⟩
  edges e := ⟨.share,e⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

noncomputable def tree : Occurrence (CanonicalTree.atDepth .term 2 d) (afterRead T d) :=
  (distributor T d).comp (BoxPullWeakening.ReverseComponents.serialLeft _ _)

theorem boundary (i : Fin [Wire.term].length) :
    (tree T d).ports (.output i) = (numeralOccurrence T d).ports (.input i) := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  cases d <;> rfl

theorem disjoint : ∀ e a, (tree T d).edges e ≠ (numeralOccurrence T d).edges a := by
  cases d <;> intro e a eq <;> cases eq

/-- The selected component is the full canonical distributor and the actual
stored numeral, preserving all other store/instance/atom-tree edges. -/
noncomputable def occurrence :
    Occurrence (CopyRule.before (ContractionTree.canonical .term 2) (numeral d)) (afterRead T d) :=
  Occurrence.SerialJoin.occurrence (tree T d) (numeralOccurrence T d) (boundary T d) (disjoint T d)

theorem token : (occurrence T d).ports (.input ⟨1,by simp⟩) =
    (.input ⟨0,by simp [Dereference.inputs]⟩ : (afterRead T d).Vertex) := by
  unfold occurrence
  rw [Occurrence.SerialJoin.occurrence_input]
  change BoundarySerial.leftInsert (Dereference.after T d) (numeral d) (Dereference.inputPort h 0) = _
  exact left_input _ _ _

noncomputable def reduct : Hypernet d (Dereference.inputs h) [] :=
  CompleteMatchCut.replaceWith (occurrence T d).matchEmbedding (occurrence T d).label
    (CopyingSelectedInput.after (ContractionTree.canonical .term 2) (numeral d) ⟨1,by simp⟩)

noncomputable def resume : (reduct T d).Vertex :=
  CompleteMatchCut.replacePort (occurrence T d).matchEmbedding (occurrence T d).label
    (CopyingSelectedInput.after (ContractionTree.canonical .term 2) (numeral d) ⟨1,by simp⟩) (.input ⟨1,by simp⟩)

/-- This is the same original copying rule, at the actual reader input. -/
theorem rewrite : Rewrite (afterRead T d) (.input ⟨0,by simp [Dereference.inputs]⟩)
    (reduct T d) (resume T d) := by
  have actual := (occurrence T d).rewrite
    (CopyingSelectedInput.rewrite (ContractionTree.canonical .term 2) (numeral d) ⟨1,by simp⟩ (.constant d (.nat 1)))
  simpa only [token,reduct,resume] using actual

/-- The existing three-transition endpoint and the full canonical target are
actual recursively isomorphic pointed states, by proved successor coherence. -/
theorem coherent : Nonempty (StateIso
    ⟨afterCopy T d,(.search,ReadTail.resume T d)⟩ ⟨reduct T d,(.search,resume T d)⟩) :=
  rewrite_deterministic (copy_rewrite T d) (rewrite T d)

/-- The complete canonical presentation has the same exact three-transition
read/request/copy prefix; none of the original weakening edges is removed. -/
theorem run : (machine d (Dereference.inputs h) []).Steps 3
    ⟨before T d,(.rewrite,.input ⟨0,by simp [Dereference.inputs]⟩)⟩
    ⟨reduct T d,(.search,resume T d)⟩ :=
  .cons (read_step T d) (.cons (request_step T d) (.cons (.rewrite (rewrite T d)) (.zero _)))

end Hypernets.Copying.Parametricity.ReadTail.FullCopy

import Hypernets.Copying.SharingTreeFillings
import Hypernets.Copying.ContractionAlgebraLaws

/-! The general tree relation used by the paper's maximal-sharing argument.
Every pair retains its actual common ordered interface and concrete trees. -/
namespace Hypernets.Copying.SharingTreeAlgebra
open Graph

theorem focusFree {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) :
    FocusFree G ∧ FocusFree H := by
  obtain ⟨s,m,_,_,left,right⟩ := pair.shape
  constructor
  · intro e; rcases left e with eq | eq
    all_goals rw [eq]; cases d <;> intro mode bad <;> cases bad
  · intro e; rcases right e with eq | eq
    all_goals rw [eq]; cases d <;> intro mode bad <;> cases bad

theorem holeFree {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) :
    HoleFree G ∧ HoleFree H := by
  cases pair with
  | trees A B f g => exact ⟨(allLabels_iso_iff _ f).mpr (ContractionAlgebra.tree_holeFree A _),
      (allLabels_iso_iff _ g).mp (ContractionAlgebra.tree_holeFree B _)⟩

/-- This relation compares genuine finite contraction trees of one fixed sort
and ordered interface, not arbitrary graphs with the same vertex count. -/
def template : PreTemplate where
  Rel := SharingTreePair
  focus_free pair := focusFree pair

theorem template_sharingTrees : template.SharingTrees := fun pair => pair

theorem template_outputClosed : template.OutputClosed := template_sharingTrees.outputClosed

theorem template_paddingClosed : template.PaddingClosed := @SharingTreePair.raise

/-- Every actual pair of primitive sharing trees is a literal relation instance. -/
theorem literal {s m} (A B : ContractionTree s m) (d : Nat) :
    template.Rel (A.atDepth d) (B.atDepth d) :=
  .trees A B (DeepIso.refl _) (DeepIso.refl _)

/-- Fully checked sharing-graph presentations provide the same literal
relation after the proved conversion to concrete primitive trees. -/
theorem graphs {d s m} {G H : Hypernet d (List.replicate m s.wire) [s.wire]}
    (left : SharingTreeGraph s m G) (right : SharingTreeGraph s m H) : template.Rel G H :=
  .trees left.tree right.tree left.treeIso.symm right.treeIso

end Hypernets.Copying.SharingTreeAlgebra

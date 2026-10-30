import Hypernets.Copying.CommonContextCut
import Hypernets.Copying.PrimitiveContextOccurrence

/-! Reindexing a selected original boundary commutes with its normalized
original filling. No wire or incidence is changed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Opening
variable {d I O J K} (C : Hypernet d I O) {A : Hypernet d J K} (f : Occurrence A C)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

/-- Boundary equalities transport the exact selected filling on either side. -/
noncomputable def reboundarySourceIso {J' K'} (hi : J = J') (ho : K = K') :
    DeepIso ((skeleton C (f.reboundarySource hi ho)).expand (localFamily C (f.reboundarySource hi ho) F))
      (((skeleton C f).expand (localFamily C f F)).reboundary hi ho) := by
  cases hi; cases ho
  rw [Net.reboundary_refl ((skeleton C f).expand (localFamily C f F))]
  refine {
    vertices := Bijection.refl _
    edges := Bijection.refl _
    internal_label := ?_
    edge_label := fun _ => labelEquiv_refl _ _
    source := ?_
    target := ?_ }
  · rintro (v | ⟨e,v⟩) <;> rfl
  · rintro ⟨e,x⟩
    change (((F (f.edges e)).source x).map _).map (Port.map id) = _
    rw [List.map_id'' (fun v => by cases v <;> rfl)]
    apply List.map_congr_left
    intro v _
    cases v with
    | internal x => rfl
    | input i =>
      simp only [Net.Expansion.insert,Net.sourcePort,skeleton,Net.relabelEdges,Net.reboundary,List.getElem_map,
        Port.cast,Bijection.refl,id_eq]
      cases (A.source e)[i.val]'(by rw [A.source_length,labelEquiv_input d (f.label e)]; exact i.isLt) <;> rfl
    | output i =>
      simp only [Net.Expansion.insert,Net.targetPort,skeleton,Net.relabelEdges,Net.reboundary,List.getElem_map,
        Port.cast,Bijection.refl,id_eq]
      cases (A.target e)[i.val]'(by rw [A.target_length,labelEquiv_output d (f.label e)]; exact i.isLt) <;> rfl
  · rintro ⟨e,x⟩
    change (((F (f.edges e)).target x).map _).map (Port.map id) = _
    rw [List.map_id'' (fun v => by cases v <;> rfl)]
    apply List.map_congr_left
    intro v _
    cases v with
    | internal x => rfl
    | input i =>
      simp only [Net.Expansion.insert,Net.sourcePort,skeleton,Net.relabelEdges,Net.reboundary,List.getElem_map,
        Port.cast,Bijection.refl,id_eq]
      cases (A.source e)[i.val]'(by rw [A.source_length,labelEquiv_input d (f.label e)]; exact i.isLt) <;> rfl
    | output i =>
      simp only [Net.Expansion.insert,Net.targetPort,skeleton,Net.relabelEdges,Net.reboundary,List.getElem_map,
        Port.cast,Bijection.refl,id_eq]
      cases (A.target e)[i.val]'(by rw [A.target_length,labelEquiv_output d (f.label e)]; exact i.isLt) <;> rfl

end Hypernets.Copying.CommonContextCut

import Hypernets.Copying.CommonContextCut
import Hypernets.Copying.ExpansionOccurrenceJoin
import Hypernets.Graph.ExpansionAssociativity

/-! Grouping an original common-context cut commutes with any finite frame,
including store frames with original template holes in their tree slots. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph Opening
variable {d I O J K} (C : Hypernet d I O) (A : Hypernet d J K)
    (D : (e : A.Edge) → Hypernet d ((alphabet d).signature.input (A.edgeLabel e))
      ((alphabet d).signature.output (A.edgeLabel e)))
    (f : ∀ e, Occurrence (D e) C) (host : A.Vertex → C.Vertex)
    (input : ∀ e i, (f e).ports (.input i) = host (A.sourcePort e i))
    (output : ∀ e i, (f e).ports (.output i) = host (A.targetPort e i))
    (disjoint : ∀ e a, e ≠ a → ∀ b c, (f e).edges b ≠ (f a).edges c)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

/-- Original fillings of a complete frame occurrence regroup into exactly
the original fillings of its complete component occurrences. -/
noncomputable def expansionIso : DeepIso
    ((skeleton C (Occurrence.ExpansionJoin.occurrence A D f host input output disjoint)).expand
      (localFamily C (Occurrence.ExpansionJoin.occurrence A D f host input output disjoint) F))
    (A.expand (fun e => (skeleton C (f e)).expand (localFamily C (f e) F))) := by
  let grouped := (A.expand (fun e => skeleton C (f e))).expand
    (Net.ExpansionAssoc.flat A (fun e => skeleton C (f e)) (fun e => localFamily C (f e) F))
  let first : DeepIso
      ((skeleton C (Occurrence.ExpansionJoin.occurrence A D f host input output disjoint)).expand
        (localFamily C (Occurrence.ExpansionJoin.occurrence A D f host input output disjoint) F)) grouped := {
    vertices := Bijection.refl _
    edges := Bijection.refl _
    internal_label := by
      rintro (a | ⟨⟨e,b⟩,v⟩)
      · cases a <;> rfl
      · rfl
    edge_label := fun _ => labelEquiv_refl _ _
    source := by
      rintro ⟨⟨e,a⟩,b⟩
      change (((F ((f e).edges a)).source b).map _).map (Port.map id) = _
      rw [List.map_id'' (fun v => by cases v <;> rfl)]
      apply List.map_congr_left
      intro v _
      cases v with
      | internal x => rfl
      | input i =>
        have bound : i.val < ((D e).source a).length := by
          rw [(D e).source_length,labelEquiv_input d ((f e).label a)]
          exact i.isLt
        simp only [Net.Expansion.insert,Net.sourcePort,Net.targetPort,skeleton,Net.relabelEdges,
          Net.expand,Net.Expansion.source,List.getElem_map,Bijection.refl,id_eq]
        cases row : ((D e).source a)[i.val]'bound <;> rfl
      | output i =>
        have bound : i.val < ((D e).target a).length := by
          rw [(D e).target_length,labelEquiv_output d ((f e).label a)]
          exact i.isLt
        simp only [Net.Expansion.insert,Net.sourcePort,Net.targetPort,skeleton,Net.relabelEdges,
          Net.expand,Net.Expansion.target,List.getElem_map,Bijection.refl,id_eq]
        cases row : ((D e).target a)[i.val]'bound <;> rfl
    target := by
      rintro ⟨⟨e,a⟩,b⟩
      change (((F ((f e).edges a)).target b).map _).map (Port.map id) = _
      rw [List.map_id'' (fun v => by cases v <;> rfl)]
      apply List.map_congr_left
      intro v _
      cases v with
      | internal x => rfl
      | input i =>
        have bound : i.val < ((D e).source a).length := by
          rw [(D e).source_length,labelEquiv_input d ((f e).label a)]
          exact i.isLt
        simp only [Net.Expansion.insert,Net.sourcePort,Net.targetPort,skeleton,Net.relabelEdges,
          Net.expand,Net.Expansion.source,List.getElem_map,Bijection.refl,id_eq]
        cases row : ((D e).source a)[i.val]'bound <;> rfl
      | output i =>
        have bound : i.val < ((D e).target a).length := by
          rw [(D e).target_length,labelEquiv_output d ((f e).label a)]
          exact i.isLt
        simp only [Net.Expansion.insert,Net.sourcePort,Net.targetPort,skeleton,Net.relabelEdges,
          Net.expand,Net.Expansion.target,List.getElem_map,Bijection.refl,id_eq]
        cases row : ((D e).target a)[i.val]'bound <;> rfl }
  exact first.trans (DeepIso.ofIso (Net.ExpansionAssoc.iso A (fun e => skeleton C (f e))
    (fun e => localFamily C (f e) F)))

end Hypernets.Copying.CommonContextCut

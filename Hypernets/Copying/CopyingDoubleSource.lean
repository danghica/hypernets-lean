import Hypernets.Copying.CopyingDoubleResources
import Hypernets.Copying.OccurrenceCoverIso

/-! Exact normalization of the original two-copy target. A complete occurrence
of the common frame exhausts the actual original edges, so its isomorphism is
proved from incidence and finite carrier coverage. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Source
open Graph Opening
variable {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))

noncomputable def payload (b : Fin 3) : Occurrence H (afterSecond T H) :=
  if b.val = 0 then Components.first T H else
    if b.val = 1 then Components.second T H else Components.third T H

noncomputable def each (e : (Frame.graph n k h d).Edge) :
    Occurrence (Frame.family H (CopyRule.residualTree (CopyRule.residualTree T)) false e) (afterSecond T H) := by
  cases d <;> rcases e with b | (j | i)
  all_goals first | exact payload T H b | exact Components.tree T H | exact Components.row T H i

noncomputable def host : (Frame.graph n k h d).Vertex → (afterSecond T H).Vertex
  | .input i => .input i
  | .output i => .output i
  | .internal (.inl (b,i)) => (payload T H b).ports (.output i)
  | .internal (.inr _) => (Components.third T H).ports (.input 0)

theorem input (e : (Frame.graph n k h d).Edge) (i) :
    (each T H e).ports (.input i) = host T H ((Frame.graph n k h d).sourcePort e i) := by
  cases d <;> rcases e with b | (j | r)
  all_goals simp only [Frame.graph,Net.relabel,Frame.net,Net.sourcePort,Frame.source,
    List.getElem_map,List.getElem_finRange]
  all_goals first
    | (change Fin 1 at i
       have zero : i=0 := Subsingleton.elim _ _
       subst i
       rcases Frame.triple b with rfl | rfl | rfl
       · exact Components.first_input T H
       · exact Components.second_input T H
       · rfl)
    | (change Fin (List.replicate n Wire.term).length at i
       exact Components.tree_input T H i)
    | (change Fin 3 at i
       exact Components.row_input T H r i)

theorem output (e : (Frame.graph n k h d).Edge) (i) :
    (each T H e).ports (.output i) = host T H ((Frame.graph n k h d).targetPort e i) := by
  cases d <;> rcases e with b | (j | r)
  all_goals simp only [Frame.graph,Net.relabel,Frame.net,Net.targetPort,Frame.target,
    List.getElem_map,List.getElem_finRange]
  all_goals first
    | (change Fin (environmentInterface k h).length at i
       rfl)
    | (change Fin 1 at i
       have zero : i=0 := Subsingleton.elim _ _
       subst i
       exact Components.tree_output T H)
    | (change Fin 1 at i
       have zero : i=0 := Subsingleton.elim _ _
       subst i
       exact Components.row_output T H r)


theorem payloads_disjoint (b c : Fin 3) (different : b ≠ c) :
    ∀ e a, (payload T H b).edges e ≠ (payload T H c).edges a := by
  cases d
  all_goals
    rcases Frame.triple b with rfl | rfl | rfl
    all_goals rcases Frame.triple c with rfl | rfl | rfl
    all_goals intro e a eq
    all_goals first | exact different rfl | cases eq

theorem payload_tree_disjoint (b : Fin 3) :
    ∀ e a, (payload T H b).edges e ≠ (Components.tree T H).edges a := by
  cases d
  all_goals
    rcases Frame.triple b with rfl | rfl | rfl
    all_goals intro e a eq; cases eq

theorem payload_row_disjoint (b : Fin 3) (i : Frame.Resource k h) :
    ∀ e a, (payload T H b).edges e ≠ (Components.row T H i).edges a := by
  cases d
  all_goals
    rcases Frame.triple b with rfl | rfl | rfl
    all_goals rintro e ⟨c,a⟩ eq; cases c <;> cases eq

theorem tree_row_disjoint (i : Frame.Resource k h) :
    ∀ e a, (Components.tree T H).edges e ≠ (Components.row T H i).edges a := by
  cases d
  all_goals rintro e ⟨c,a⟩ eq; cases c <;> cases eq

theorem disjoint (e a : (Frame.graph n k h d).Edge) (different : e ≠ a) :
    ∀ b c, (each T H e).edges b ≠ (each T H a).edges c := by
  cases d
  all_goals
    rcases e with e | (e | e)
    all_goals rcases a with a | (a | a)
    · exact payloads_disjoint T H e a (fun eq => different (congrArg Sum.inl eq))
    · exact payload_tree_disjoint T H e
    · exact payload_row_disjoint T H e a
    · exact fun b c eq => payload_tree_disjoint T H a c b eq.symm
    · exact False.elim (different (congrArg (fun j => Sum.inr (Sum.inl j)) (Subsingleton.elim _ _)))
    · exact tree_row_disjoint T H a
    · exact fun b c eq => payload_row_disjoint T H a e c b eq.symm
    · exact fun b c eq => tree_row_disjoint T H e c b eq.symm
    · exact Components.rows_disjoint T H e a (fun eq => different (congrArg (fun j => Sum.inr (Sum.inr j)) eq))

/-- The common normal graph is a complete-label occurrence in the actual
original target, with the original external boundary fixed pointwise. -/
noncomputable def occurrence :
    Occurrence (Frame.normal H (CopyRule.residualTree (CopyRule.residualTree T)) false) (afterSecond T H) :=
  Occurrence.ExpansionJoin.occurrence _ _ (each T H) (host T H) (input T H) (output T H) (disjoint T H)


/-- Every original edge belongs to exactly the retained payload, remaining
tree, or nested-resource component described by the common frame. -/
theorem cover (e : (afterSecond T H).Edge) :
    ∃ a, (occurrence T H).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨outer,e⟩
    cases outer
    · rcases e with ⟨branch,e⟩
      cases branch
      · exact ⟨⟨.inl 0,e⟩,rfl⟩
      · rcases e with ⟨inner,e⟩
        cases inner
        · rcases e with ⟨branch,e⟩
          cases branch
          · exact ⟨⟨.inl 1,e⟩,rfl⟩
          · rcases e with ⟨side,e⟩
            cases side
            · exact ⟨⟨.inr (.inl 0),e⟩,rfl⟩
            · exact ⟨⟨.inl 2,e⟩,rfl⟩
        · obtain ⟨i,a,eq⟩ := Components.resource_cover e
          refine ⟨⟨.inr (.inr i),⟨false,a⟩⟩,?_⟩
          change (Components.retained T H).edges ((Occurrence.serialRight _ _).edges ((Components.resource i).edges a)) = _
          rw [eq]
          rfl
    · obtain ⟨i,a,eq⟩ := Components.resource_cover e
      refine ⟨⟨.inr (.inr i),⟨true,a⟩⟩,?_⟩
      change (Occurrence.serialRight _ _).edges ((Components.resource i).edges a) = _
      rw [eq]
      rfl

/-- Exact original-graph normalization. All canonical rows, three payload
copies, and both inserted weakenings of the remaining tree are preserved. -/
noncomputable def iso :
    DeepIso (Frame.normal H (CopyRule.residualTree (CopyRule.residualTree T)) false) (afterSecond T H) :=
  (occurrence T H).iso_of_edge_surjective (fun _ => rfl) (fun _ => rfl) (cover T H)

end Hypernets.Copying.CopyingDouble.Source

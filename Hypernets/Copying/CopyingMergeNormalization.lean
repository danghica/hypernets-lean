import Hypernets.Copying.CopyingMergeComponents
import Hypernets.Copying.ExpansionOccurrenceJoin
import Hypernets.Copying.OccurrenceCoverIso

/-! Complete incidence normalization of actual nested merges into one common
three-branch frame. The external input order remains A, then B, then C. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.CopyingMerge.Normalization
open Graph Opening
variable {d a b c k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (C : Hypernet d (List.replicate c .term) (environmentInterface k h)) (r : Bool)

noncomputable def components (e : (Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).Edge) :
    Occurrence (Frame.family (Inputs.bijection a b c) (branches A B C) r e) (Components.target A B C r) := by
  cases d <;> rcases e with tag | i
  all_goals first | exact Components.branch A B C r tag | exact Components.row A B C r i

noncomputable def host : (Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).Vertex →
    (Components.target A B C r).Vertex
  | .input i => .input i
  | .output i => .output i
  | .internal (tag,i) => (Components.branch A B C r tag).ports (.output i)

theorem input (e : (Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).Edge)
    (i : Fin ((alphabet d).signature.input ((Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).edgeLabel e)).length) :
    (components A B C r e).ports (.input i) =
      host A B C r ((Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).sourcePort e i) := by
  cases d
  all_goals
    rcases e with tag | resource
    · change (Components.branch A B C r tag).ports (.input i) = _
      rw [Components.branch_input]
      simp only [Net.sourcePort,Frame.graph,Frame.net,Frame.source,Net.relabel,List.getElem_map,
        List.getElem_finRange,Fin.cast,Fin.eta,Frame.branchInput,host]
      apply congrArg Port.input
      apply Fin.ext
      rfl
    · change Fin 3 at i
      change (Components.row A B C r resource).ports (.input i) = _
      simp only [Net.sourcePort,Frame.graph,Frame.net,Frame.source,Net.relabel,List.getElem_map,
        List.getElem_finRange,Fin.cast,Fin.eta,Frame.rowInput,Frame.branchOutput,host]
      exact Components.row_input A B C r resource i

theorem output (e : (Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).Edge)
    (i : Fin ((alphabet d).signature.output ((Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).edgeLabel e)).length) :
    (components A B C r e).ports (.output i) =
      host A B C r ((Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d).targetPort e i) := by
  cases d
  all_goals
    rcases e with tag | resource
    · change (Components.branch A B C r tag).ports (.output i) = _
      simp only [Net.targetPort,Frame.graph,Frame.net,Frame.target,Net.relabel,List.getElem_map,
        List.getElem_finRange,Fin.cast,Fin.eta,Frame.branchOutput,host]
    · change (Components.row A B C r resource).ports (.output i) = _
      change Fin 1 at i
      have zero : i = 0 := Subsingleton.elim _ _
      subst i
      exact Components.row_output A B C r resource

theorem disjoint : ∀ e f, e ≠ f → ∀ v w,
    (components A B C r e).edges v ≠ (components A B C r f).edges w := by
  cases d
  all_goals
    intro e f ne v w eq
    rcases e with tag | i
    all_goals rcases f with other | j
    · exact Components.branches_disjoint A B C r tag other (fun same => ne (congrArg Sum.inl same)) v w eq
    · exact Components.branch_row_disjoint A B C r tag j v w eq
    · exact Components.branch_row_disjoint A B C r other i w v eq.symm
    · exact Components.rows_disjoint A B C r i j (fun same => ne (congrArg Sum.inr same)) v w eq

/-- Both original associations contain exactly the same three original
branches and the two complete canonical rows for each original resource. -/
noncomputable def occurrence : Occurrence (normal A B C r) (Components.target A B C r) :=
  Occurrence.ExpansionJoin.occurrence
    (Frame.graph (Inputs.arity a b c) (a+b+c) k h (Inputs.bijection a b c) d)
    (Frame.family (Inputs.bijection a b c) (branches A B C) r)
    (components A B C r) (host A B C r) (input A B C r) (output A B C r) (disjoint A B C r)

theorem cover : Function.Surjective (occurrence A B C r).edges := by
  cases r <;> cases d
  all_goals
    rintro ⟨outer,e⟩
    cases outer
    · rcases e with ⟨side,e⟩
      cases side
      · first
          | rcases e with ⟨inner,e⟩
            cases inner
            · rcases e with ⟨side,e⟩
              cases side
              · exact ⟨⟨.inl 0,e⟩,rfl⟩
              · exact ⟨⟨.inl 1,e⟩,rfl⟩
            · obtain ⟨i,x,eq⟩ := CopyingDouble.Components.resource_cover e
              refine ⟨⟨.inr i,⟨false,x⟩⟩,?_⟩
              change (component (net A B) C false).edges
                (Serial.rightEdge _ _ ((CopyingDouble.Components.resource i).edges x)) = _
              rw [eq]
              rfl
          | exact ⟨⟨.inl 0,e⟩,rfl⟩
      · first
          | exact ⟨⟨.inl 2,e⟩,rfl⟩
          | rcases e with ⟨inner,e⟩
            cases inner
            · rcases e with ⟨side,e⟩
              cases side
              · exact ⟨⟨.inl 1,e⟩,rfl⟩
              · exact ⟨⟨.inl 2,e⟩,rfl⟩
            · obtain ⟨i,x,eq⟩ := CopyingDouble.Components.resource_cover e
              refine ⟨⟨.inr i,⟨false,x⟩⟩,?_⟩
              change (component A (net B C) true).edges
                (Serial.rightEdge _ _ ((CopyingDouble.Components.resource i).edges x)) = _
              rw [eq]
              rfl
    · obtain ⟨i,x,eq⟩ := CopyingDouble.Components.resource_cover e
      refine ⟨⟨.inr i,⟨true,x⟩⟩,?_⟩
      first
        | change Serial.rightEdge (pair (net A B) C) _ ((CopyingDouble.Components.resource i).edges x) = _
          rw [eq]
          rfl
        | change Serial.rightEdge (pair A (net B C)) _ ((CopyingDouble.Components.resource i).edges x) = _
          rw [eq]
          rfl

/-- Complete edge coverage and the fixed whole external boundary identify
the normal frame with each actual association, for arbitrary original branches. -/
noncomputable def iso : DeepIso (normal A B C r) (Components.target A B C r) :=
  (occurrence A B C r).iso_of_edge_surjective (fun _ => rfl) (fun _ => rfl) (cover A B C r)

end Hypernets.Copying.CopyingMerge.Normalization

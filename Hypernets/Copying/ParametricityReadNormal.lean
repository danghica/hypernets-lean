import Hypernets.Copying.ParametricityReadNormalComponents

/-! Reconstruct the corrected private read as its returned numeral and an
independent retained store with the complete residual atom tree. All graph
equalities below are proved from actual occurrences and edge coverage. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail.Normal
open Graph Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

theorem tree_store_disjoint : ∀ a b, (tree T d).edges a ≠ (store T d).edges b := by
  apply (Discard.retained T d).acrossCut_disjoint
  apply (FullCopy.occurrence T d).acrossCut_disjoint
  cases d <;> intro a b eq
  all_goals have bad := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases bad

theorem tree_payload_disjoint (b : Bool) : ∀ e c, (tree T d).edges e ≠ (payload T d b).edges c := by
  apply (Discard.retained T d).acrossCut_disjoint
  cases d <;> cases b <;> intro e c eq <;> cases eq

theorem store_payload_disjoint (b : Bool) : ∀ e c, (store T d).edges e ≠ (payload T d b).edges c := by
  apply (Discard.retained T d).acrossCut_disjoint
  cases d <;> cases b <;> intro e c eq <;> cases eq

theorem payloads_disjoint : ∀ e c, (payload T d false).edges e ≠ (payload T d true).edges c := by
  apply (Discard.retained T d).acrossCut_disjoint
  cases d <;> intro e c eq
  all_goals
    have eq := Sum.inr.inj eq
    have bad := congrArg Sigma.fst eq
    cases bad

theorem weak_store_disjoint : ∀ e c, (weak T d).edges e ≠ (store T d).edges c := by
  cases d <;> intro e c eq <;> cases eq

theorem weak_payload_disjoint (b : Bool) : ∀ e c, (weak T d).edges e ≠ (payload T d b).edges c := by
  cases d <;> cases b <;> intro e c eq <;> cases eq

theorem residual_store_disjoint : ∀ e c, (residual T d).edges e ≠ (store T d).edges c := by
  intro e c eq
  rcases ((residualTree T).sharingTreeGraph d).labels e with label | label
  all_goals
    have old := (residual T d).matchEmbedding.primitive e _ label
    have fresh := (store T d).matchEmbedding.primitive c .store (by cases d <;> rfl)
    have impossible := primitiveLabel_injective d
      (old.symm.trans ((congrArg (Discard.collected T d).edgeLabel eq).trans fresh))
    cases impossible

theorem residual_payload_disjoint (b : Bool) : ∀ e c, (residual T d).edges e ≠ (payload T d b).edges c := by
  cases b <;> intro e c eq
  all_goals
    rcases ((residualTree T).sharingTreeGraph d).labels e with label | label
    all_goals
      have old := (residual T d).matchEmbedding.primitive e _ label
      have fresh := (payload T d _).matchEmbedding.primitive c (.operation (.const (.nat 1))) (by cases d <;> rfl)
      have impossible := primitiveLabel_injective d
        (old.symm.trans ((congrArg (Discard.collected T d).edgeLabel eq).trans fresh))
      cases impossible

def cell (d : Nat) : Hypernet d [.atom] [] := Serial.net (primitiveNet d .store) (numeral d)

noncomputable def cellOccurrence : Occurrence (cell d) (Discard.collected T d) :=
  Occurrence.SerialJoin.occurrence (store T d) (payload T d true) (by
    intro i
    change Fin 1 at i
    have zero : i=0 := Subsingleton.elim _ _
    subst i
    exact store_payload T d) (store_payload_disjoint T d true)

def retainedCell : Hypernet d (List.replicate (0+h) .atom) [] :=
  Serial.net ((residualTree T).atDepth d) (cell d)

noncomputable def retainedCellOccurrence : Occurrence (retainedCell T d) (Discard.collected T d) :=
  Occurrence.SerialJoin.occurrence (residual T d) (cellOccurrence T d) (by
    intro i
    change Fin 1 at i
    have zero : i=0 := Subsingleton.elim _ _
    subst i
    change (residual T d).ports (.output 0) = (cellOccurrence T d).ports (.input ⟨0,by decide⟩)
    exact (residual_output T d).trans ((tree_store T d).trans
      (Occurrence.SerialJoin.occurrence_input _ _ _ _ _).symm)) (by
      cases d <;> intro e c <;> rcases c with ⟨b,c⟩ <;> cases b
      all_goals first | exact residual_store_disjoint T _ e c | exact residual_payload_disjoint T _ true e c)

theorem active_cell_disjoint : ∀ e c,
    (payload T d false).edges e ≠ (retainedCellOccurrence T d).edges c := by
  cases d <;> intro e c <;> rcases c with ⟨b,c⟩ <;> cases b
  all_goals first
    | exact fun eq => residual_payload_disjoint T _ false c e eq.symm
    | (rcases c with ⟨b,c⟩; cases b
       · exact fun eq => store_payload_disjoint T _ false c e eq.symm
       · exact payloads_disjoint T _ e c)

def net : Hypernet d (Dereference.inputs h) [] :=
  (Net.Tensor.net (numeral d) (retainedCell T d)).reboundary
    (by simp [Dereference.inputs]) (by simp [environmentInterface])

noncomputable def parallelOccurrence :
    Occurrence (Net.Tensor.net (numeral d) (retainedCell T d)) (Discard.collected T d) :=
  Occurrence.ParallelJoin.occurrence (Net.Tensor.family (numeral d) (retainedCell T d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => by cases b; exact payload T d false; exact retainedCellOccurrence T d) (by
      intro a b ne e c
      cases a <;> cases b
      all_goals first
        | exact False.elim (ne rfl)
        | exact active_cell_disjoint T d e c
        | exact fun eq => active_cell_disjoint T d c e eq.symm)

noncomputable def normalOccurrence : Occurrence (net T d) (Discard.collected T d) :=
  (parallelOccurrence T d).reboundarySource (by simp [Dereference.inputs]) (by simp [environmentInterface])

theorem original_tree_input (i : Fin h) :
    (originalTree T d).ports (.input ⟨i.val+1,by simp <;> omega⟩) =
      .input ⟨i.val+1,by simp [Dereference.inputs] <;> omega⟩ := by
  cases d
  all_goals
    simp [originalTree,BoxPullWeakening.ReverseComponents.serialLeft,Opening.Occurrence.comp,
      Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Dereference.afterFrame,
      Dereference.afterSource,Dereference.otherInputs,Dereference.inputPort,
      List.getElem_map,List.getElem_finRange,Port.map]
  case zero => exact Combined.left_input (Dereference.after T 0) (numeral 0) _
  case succ d => exact Combined.left_input (Dereference.after T (d+1)) (numeral (d+1)) _

theorem tree_input (i : Fin h) : (tree T d).ports (.input ⟨i.val+1,by simp <;> omega⟩) =
    .input ⟨i.val+1,by simp [Dereference.inputs] <;> omega⟩ :=
  (Discard.retained T d).acrossCut_externalInput (separatedTree T d) (retained_tree_disjoint T d)
    (GarbageCollection.right d 0 1) _ _
    ((FullCopy.occurrence T d).acrossCut_externalInput (originalTree T d) (content_tree_disjoint T d)
      (ClosedCopyPair.selectedPair (numeral d) 1) _ _ (original_tree_input T d i))

theorem residual_input (i : Fin (List.replicate (0+h) Wire.atom).length) :
    (residual T d).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp_all [Dereference.inputs]⟩ := by
  let j : Fin h := ⟨i.val,by simpa using i.isLt⟩
  have position : ContractionTree.Graft.rightInsert ((ContractionTree.canonical .atom 0).atDepth d)
      (T.atDepth d) 0 (.input ⟨j.val+1,by simp <;> omega⟩) = .input i := by
    rw [ContractionTree.Graft.right_input]
    simp [ContractionTree.Graft.downstream,j,Port.map]
  change (ContractionTree.Graft.Join.occurrence (weak T d) (tree T d) 0
    (weak_tree T d) (weak_tree_disjoint T d)).ports (.input i) = _
  rw [← position,ContractionTree.Graft.Join.right_port]
  exact tree_input T d j

end Hypernets.Copying.Parametricity.ReadTail.Normal

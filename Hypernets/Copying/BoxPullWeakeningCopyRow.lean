import Hypernets.Copying.BoxPullWeakeningRowOccurrence

/-! Identify the unchanged selected distributor row in the full original
copy reduct of a payload with an added weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.CopyRow
open Graph Opening

/-- A selected row is an actual component of the original ordered forest. -/
def forestOccurrence (s : ShareSort) (k m d : Nat) (i : Fin k) :
    Occurrence (CanonicalTree.atDepth s m d) (Distributor.atDepth s k m d) where
  ports := Net.Parallel.embed (fun _ : Fin k => CanonicalTree.net s m)
    (Distributor.boundary s k m) i
  internals v := ⟨i,v⟩
  edges e := ⟨i,e⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl d _
  source _ := rfl
  target _ := rfl

/-- The term row remains in the term half of the ordered environment forest. -/
def termOccurrence (d k h : Nat) (i : Fin k) :
    Occurrence (CanonicalTree.atDepth .term 2 d) (Translation.environmentDistributor d k h 2) where
  ports v := Net.Parallel.embed
    (Net.Tensor.family (Distributor.atDepth .term k 2 d) (Distributor.atDepth .atom h 2 d))
    (Net.Tensor.boundary _ _ _ _) false ((forestOccurrence .term k 2 d i).ports v)
  internals v := ⟨false,⟨i,v⟩⟩
  edges e := ⟨false,⟨i,e⟩⟩
  internal_map _ := rfl
  internal_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  edge_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  internal_label _ := rfl
  label _ := labelEquiv_refl d _
  source e := by
    change (CanonicalTree.sources e).map _ = ((CanonicalTree.sources e).map _).map _
    rw [List.map_map]
    rfl
  target _ := rfl

/-- The atom row remains in the atom half, after every term resource. -/
def atomOccurrence (d k h : Nat) (i : Fin h) :
    Occurrence (CanonicalTree.atDepth .atom 2 d) (Translation.environmentDistributor d k h 2) where
  ports v := Net.Parallel.embed
    (Net.Tensor.family (Distributor.atDepth .term k 2 d) (Distributor.atDepth .atom h 2 d))
    (Net.Tensor.boundary _ _ _ _) true ((forestOccurrence .atom h 2 d i).ports v)
  internals v := ⟨true,⟨i,v⟩⟩
  edges e := ⟨true,⟨i,e⟩⟩
  internal_map _ := rfl
  internal_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  edge_injective := by
    intro a b eq
    exact eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2
  internal_label _ := rfl
  label _ := labelEquiv_refl d _
  source e := by
    change (CanonicalTree.sources e).map _ = ((CanonicalTree.sources e).map _).map _
    rw [List.map_map]
    rfl
  target _ := rfl

/-- BPullW selects the last term row or the first atom row, exactly matching
its insertion between the two free-resource blocks. -/
def selected (d k h : Nat) (s : ShareSort) :
    Occurrence (CanonicalTree.atDepth s 2 d)
      (Translation.environmentDistributor d (variables s k) (atoms s h) 2) := by
  cases s
  · exact termOccurrence d (k+1) h ⟨k,by omega⟩
  · exact atomOccurrence d k (h+1) ⟨0,by omega⟩

variable {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

/-- The original selected row in the complete copy reduct, not an abstract
isomorphic replacement for that reduct. -/
def row : Occurrence (CanonicalTree.atDepth s 2 d) (CopyRule.after T (extend H s)) :=
  (selected d k h s).comp (Occurrence.serialRight _ _)

def weakEdge (b : Bool) : (CopyRule.after T (extend H s)).Edge := by
  cases d
  all_goals
    exact if b then CopyRule.rightEdge T (extend H s) ⟨true,(0 : Fin 1)⟩
      else CopyRule.leftEdge T (extend H s) ⟨true,(0 : Fin 1)⟩

theorem weak_injective : Function.Injective (weakEdge T H s) := by
  cases d <;> intro a b eq <;> cases a <;> cases b <;> first | rfl | cases eq

theorem weak_disjoint (b : Bool) (e : (CanonicalTree.atDepth s 2 d).Edge) :
    weakEdge T H s b ≠ (row T H s).edges e := by
  cases d <;> cases b <;> cases s <;> intro eq <;> cases eq

theorem weak_labels (b : Bool) :
    (CopyRule.after T (extend H s)).edgeLabel (weakEdge T H s b) =
      primitiveLabel d (.weakening s) := by
  cases d <;> cases b <;> rfl

theorem weak_sources (b : Bool) :
    (CopyRule.after T (extend H s)).source (weakEdge T H s b) = [] := by
  cases d <;> cases b <;> rfl

def addedOutput (k h : Nat) (s : ShareSort) :
    Fin (environmentInterface (variables s k) (atoms s h)).length :=
  ⟨k,by cases s <;> simp [variables,atoms,environmentInterface] <;> omega⟩

theorem extended_weak_target {d k h} (H : Hypernet d [.term] (environmentInterface k h))
    (s : ShareSort) (e : (primitiveNet d (.weakening s)).Edge) :
    (extend H s).target ⟨true,e⟩ = [.output (addedOutput k h s)] := by
  cases d
  all_goals
    apply congrArg List.singleton
    apply congrArg Port.output
    exact Fin.ext ((inserted_weakening_output (I := [.term]) (A := List.replicate k .term)
      (B := List.replicate h .atom) s).trans (by simp [addedOutput]))

theorem weak_target_link (b : Bool) :
    (CopyRule.after T (extend H s)).target (weakEdge T H s b) =
      [.internal (.inl (CopyRule.copyOutput (variables s k) (atoms s h) b (addedOutput k h s)))] := by
  cases d <;> cases b
  all_goals first
    | (change (((extend H s).target ⟨true,(0 : Fin 1)⟩).map
        (CopyRule.activeInsert T (extend H s))) = _
       rw [extended_weak_target,List.map_singleton]
       unfold CopyRule.activeInsert
       rw [CopyRule.pair_output,CopyRule.serial_left_output])
    | (change (((extend H s).target ⟨true,(0 : Fin 1)⟩).map
        (CopyRule.retainedInsert T (extend H s))) = _
       rw [extended_weak_target,List.map_singleton]
       unfold CopyRule.retainedInsert
       rw [Application.right_serial_output,CopyRule.pair_output,CopyRule.serial_left_output])

theorem selected_input (b : Bool) :
    (selected d k h s).ports (.input (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩)) =
      .input (CopyRule.copyOutput (variables s k) (atoms s h) b (addedOutput k h s)) := by
  have output_eq {k h} (b : Bool) (i : Fin (environmentInterface k h).length) :
      CopyRule.copyOutput k h b i = PairBoundary.index b i := by cases b <;> rfl
  rw [output_eq]
  cases s
  · change _ = Port.input (PairBoundary.index (h := h) b
      (EnvironmentPermutation.termIndex (⟨k,by omega⟩ : Fin (k+1))))
    rw [PairBoundary.term_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;> simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
      Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.termIndex,
      PairBoundary.use]
  · change _ = Port.input (PairBoundary.index (k := k) b
      (EnvironmentPermutation.atomIndex (⟨0,by omega⟩ : Fin (h+1))))
    rw [PairBoundary.atom_index]
    cases b <;> apply congrArg Port.input <;> apply Fin.ext <;> simp [Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,
      Distributor.boundary,Distributor.inputIndex,FinGrid.index,EnvironmentPermutation.atomIndex,
      PairBoundary.use]

theorem weak_targets (b : Bool) :
    (CopyRule.after T (extend H s)).target (weakEdge T H s b) =
      [(row T H s).ports (.input (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩))] := by
  rw [weak_target_link]
  change [_] = [BoundarySerial.rightInsert _ _ ((selected d k h s).ports _)]
  rw [selected_input,CopyRule.serial_right_input]

/-- The full five-edge row is present in the actual copy reduct, with its
original ordered incidences. The other outputs and residual tree are untouched. -/
noncomputable def occurrence :
    Occurrence (IdemRow.canonical d s) (CopyRule.after T (extend H s)) :=
  IdemRow.attachedOccurrence (row T H s) (weakEdge T H s) (weak_injective T H s)
    (weak_disjoint T H s) (weak_labels T H s) (weak_sources T H s) (weak_targets T H s)

/-- Exact first whole-graph intermediate after collapsing the inner Idem. -/
noncomputable def intermediate :=
  CompleteMatchCut.replaceWith (occurrence T H s).matchEmbedding (occurrence T H s).label
    (ContractionIdempotence.left d s)

/-- Exact second whole-graph intermediate after collapsing the root Idem. -/
noncomputable def corrected :=
  CompleteMatchCut.replaceWith (occurrence T H s).matchEmbedding (occurrence T H s).label
    (primitiveNet d (.weakening s))

theorem reduct_free (free : FocusFree H) : FocusFree (CopyRule.after T (extend H s)) :=
  CopyRule.focusFree_after T _ ((extend_allLabels _ H s).mpr
    ⟨free,by intro m eq; cases eq⟩)

/-- First genuine Idem filling witness for the entire original copy reduct. -/
noncomputable def first (free : FocusFree H) :
    FillingWitness ContractionIdempotence.template
      (CopyRule.after T (extend H s)) (intermediate T H s) :=
  IdemRow.cut_first (occurrence T H s) (reduct_free T H s free)

/-- Second genuine Idem witness retains exactly the same constructed host
complement. This is a certified chain, without assuming witness transitivity. -/
noncomputable def second (free : FocusFree H) :
    FillingWitness ContractionIdempotence.template
      (intermediate T H s) (corrected T H s) :=
  IdemRow.cut_second (occurrence T H s) (reduct_free T H s free)

end Hypernets.Copying.BoxPullWeakening.CopyRow

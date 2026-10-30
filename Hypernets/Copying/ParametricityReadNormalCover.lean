import Hypernets.Copying.ParametricityReadNormal

/-! Exhaustive finite-edge coverage of the reconstructed private-read
residual. No leftover store, sharing, or reference edge is silently erased. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail.Normal
open Graph Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

theorem retainedCell_input (i : Fin (List.replicate (0+h) Wire.atom).length) :
    (retainedCellOccurrence T d).ports (.input i) =
      .input ⟨i.val+1,by have := i.isLt; simp_all [Dereference.inputs]⟩ :=
  (Occurrence.SerialJoin.occurrence_input _ _ _ _ i).trans (residual_input T d i)

theorem parallel_input (i : Fin ([Wire.term] ++ List.replicate (0+h) Wire.atom).length) :
    (parallelOccurrence T d).ports (.input i) =
      .input ⟨i.val,by have := i.isLt; simpa [Dereference.inputs] using this⟩ := by
  let B := Net.Tensor.boundary [Wire.term] (environmentInterface 0 0)
    (List.replicate (0+h) Wire.atom) []
  have surj : ∃ x, B.inputs.toFun x = i := ⟨B.inputs.invFun i,B.inputs.right_inv i⟩
  obtain ⟨⟨b,k⟩,eq⟩ := surj
  subst i
  change (parallelOccurrence T d).ports
    (Net.Parallel.embed (Net.Tensor.family (numeral d) (retainedCell T d)) B b (.input k)) = _
  unfold parallelOccurrence
  rw [Occurrence.ParallelJoin.occurrence_embed]
  cases b
  · change Fin 1 at k
    have zero : k=0 := Subsingleton.elim _ _
    subst k
    exact active_input T d
  · exact (retainedCell_input T d k).trans (congrArg Port.input (Fin.ext (Nat.add_comm _ _)))

theorem normal_input (i : Fin (Dereference.inputs h).length) :
    (normalOccurrence T d).ports (.input i) = .input i :=
  parallel_input T d ⟨i.val,by have := i.isLt; simpa [Dereference.inputs] using this⟩

/-- The literal read graph consists of exactly its full content-copy match,
the discarded instance, the retained atom tree and the retained store. -/
theorem original_cover (e : (afterRead T d).Edge) :
    (∃ a, (FullCopy.occurrence T d).edges a = e) ∨
    (∃ a, (Discard.occurrence T d).edges a = e) ∨
    (∃ a, (originalTree T d).edges a = e) ∨
    (∃ a, (originalStore T d).edges a = e) := by
  cases d
  all_goals
    rcases e with ⟨b,e⟩
    cases b
    · rcases e with ⟨b,e⟩
      cases b
      · right; left
        change Fin 1 at e
        have zero : e=(0 : Fin 1) := Subsingleton.elim _ _
        subst e
        exact ⟨⟨false,(0 : Fin 1)⟩,rfl⟩
      · change Fin 1 at e
        have zero : e=0 := Subsingleton.elim _ _
        subst e
        exact .inr (.inl ⟨⟨true,(0 : Fin 1)⟩,rfl⟩)
      · exact .inr (.inr (.inl ⟨e,rfl⟩))
      · change Fin 1 at e
        have zero : e=0 := Subsingleton.elim _ _
        subst e
        exact .inr (.inr (.inr ⟨(0 : Fin 1),rfl⟩))
      · exact .inl ⟨⟨false,e⟩,rfl⟩
    · exact .inl ⟨⟨true,e⟩,rfl⟩

/-- The first cut removes precisely the complete stored-content match and
retains each other original component alongside the two separated numerals. -/
theorem separated_cover (e : (FullCopy.separated T d).Edge) :
    (∃ a, (Discard.retained T d).edges a = e) ∨
    (∃ a, (separatedTree T d).edges a = e) ∨
    (∃ a, (separatedStore T d).edges a = e) ∨
    ∃ b a, (separatedPayload T d b).edges a = e := by
  cases e with
  | inl e =>
    rcases e with ⟨old,notHole⟩
    cases old with
    | none => exact False.elim (notHole rfl)
    | some old =>
      rcases old with ⟨old,unmatched⟩
      rcases original_cover T d old with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩
      · exact False.elim (unmatched a eq)
      · subst old; exact .inl ⟨a,rfl⟩
      · subst old; exact .inr (.inl ⟨a,rfl⟩)
      · subst old; exact .inr (.inr (.inl ⟨a,rfl⟩))
  | inr e =>
    right; right; right
    cases d
    all_goals
      rcases e with ⟨b,e⟩
      refine ⟨b,e,?_⟩
      cases b <;> rfl

/-- The second cut removes precisely the consumed instance and inserts the
one atom weakening. The store, tree and both numeral copies exhaust the rest. -/
theorem collected_cover (e : (Discard.collected T d).Edge) :
    (∃ a, (weak T d).edges a = e) ∨
    (∃ a, (tree T d).edges a = e) ∨
    (∃ a, (store T d).edges a = e) ∨
    ∃ b a, (payload T d b).edges a = e := by
  cases e with
  | inl e =>
    rcases e with ⟨old,notHole⟩
    cases old with
    | none => exact False.elim (notHole rfl)
    | some old =>
      rcases old with ⟨old,unmatched⟩
      rcases separated_cover T d old with ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨a,eq⟩ | ⟨b,a,eq⟩
      · exact False.elim (unmatched a eq)
      · subst old; exact .inr (.inl ⟨a,rfl⟩)
      · subst old; exact .inr (.inr (.inl ⟨a,rfl⟩))
      · subst old; exact .inr (.inr (.inr ⟨b,a,rfl⟩))
  | inr e =>
    left
    have same := (collectedCopy d).only e
    cases d
    all_goals
      change e = ⟨true,⟨(0 : Fin 1),(0 : Fin 1)⟩⟩ at same
      subst e
      exact ⟨(0 : Fin 1),rfl⟩

theorem residual_covers_weak (e : ((ContractionTree.canonical .atom 0).atDepth d).Edge) :
    ∃ a, (residual T d).edges a = (weak T d).edges e := by
  let iso := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) T 0 d
  let x := (ContractionTree.Graft.leftOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
    (T.atDepth d) 0).edges e
  refine ⟨iso.edges.invFun x,?_⟩
  change (ContractionTree.Graft.Join.occurrence (weak T d) (tree T d) 0
    (weak_tree T d) (weak_tree_disjoint T d)).edges (iso.edges.toFun (iso.edges.invFun x)) = _
  rw [iso.edges.right_inv]
  exact ContractionTree.Graft.Join.left_edge _ _ _ _ _ e

theorem residual_covers_tree (e : (T.atDepth d).Edge) :
    ∃ a, (residual T d).edges a = (tree T d).edges e := by
  let iso := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) T 0 d
  let x := (ContractionTree.Graft.rightOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
    (T.atDepth d) 0).edges e
  refine ⟨iso.edges.invFun x,?_⟩
  change (ContractionTree.Graft.Join.occurrence (weak T d) (tree T d) 0
    (weak_tree T d) (weak_tree_disjoint T d)).edges (iso.edges.toFun (iso.edges.invFun x)) = _
  rw [iso.edges.right_inv]
  exact ContractionTree.Graft.Join.right_edge _ _ _ _ _ e

theorem normal_covers_residual (e : ((residualTree T).atDepth d).Edge) :
    ∃ a, (normalOccurrence T d).edges a = (residual T d).edges e := by
  cases d <;> exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩

theorem normal_covers_store (e : (primitiveNet d .store).Edge) :
    ∃ a, (normalOccurrence T d).edges a = (store T d).edges e := by
  cases d <;> exact ⟨⟨true,⟨true,⟨false,e⟩⟩⟩,rfl⟩

theorem normal_covers_payload (b : Bool) (e : (Net.Tensor.family (numeral d) (numeral d) b).Edge) :
    ∃ a, (normalOccurrence T d).edges a = (payload T d b).edges e := by
  cases d <;> cases b
  all_goals first | exact ⟨⟨false,e⟩,rfl⟩ | exact ⟨⟨true,⟨true,⟨true,e⟩⟩⟩,rfl⟩

/-- Every corrected edge is accounted for by the reconstructed returned
value or retained store; the complete occurrence is therefore surjective. -/
theorem normal_cover (e : (Discard.collected T d).Edge) :
    ∃ a, (normalOccurrence T d).edges a = e := by
  rcases collected_cover T d e with ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨b,a,rfl⟩
  · obtain ⟨b,eq⟩ := residual_covers_weak T d a
    obtain ⟨c,cover⟩ := normal_covers_residual T d b
    exact ⟨c,cover.trans eq⟩
  · obtain ⟨b,eq⟩ := residual_covers_tree T d a
    obtain ⟨c,cover⟩ := normal_covers_residual T d b
    exact ⟨c,cover.trans eq⟩
  · exact normal_covers_store T d a
  · exact normal_covers_payload T d b a

/-- The final corrected graph is exactly the returned numeral in parallel
with the remaining private store. No observational quotient is used here. -/
noncomputable def iso : DeepIso (net T d) (Discard.collected T d) :=
  (normalOccurrence T d).iso_of_edge_surjective (normal_input T d)
    (fun i => Fin.elim0 i) (normal_cover T d)

end Hypernets.Copying.Parametricity.ReadTail.Normal

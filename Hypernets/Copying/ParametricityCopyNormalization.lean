import Hypernets.Copying.ParametricityCopyComponents
import Hypernets.Copying.ParametricityCopyContext
import Hypernets.Copying.OccurrenceCoverIso

/-! The actual original copying target is exactly an enlarged two-abstraction
family inside the common residual-input context. This retains every canonical
resource edge and allows arbitrary residual input arity, including zero. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyNormalization
open Graph Opening
variable {d a k h : Nat}
    (P : Hypernet d (List.replicate a .term) [.term])
    (H : Hypernet d [.term] (environmentInterface k h))

noncomputable def rawOccurrence :
    Occurrence (ContractionTree.Graft.net (s := .term) (b := 1) P (CopyingMerge.net (a := 1) (b := 1) H H) 1)
      (CopyComponents.target P H) :=
  ContractionTree.Graft.Join.occurrence (CopyComponents.upstream P H)
    (CopyComponents.duplicate P H) 1 (by simpa only [Fin.val_one] using CopyComponents.upstream_link P H)
    (CopyComponents.upstream_duplicate_disjoint P H)

theorem raw_input (i : Fin (List.replicate (a+1) Wire.term).length) :
    (rawOccurrence P H).ports (.input i) = .input ((CopyContext.rotation a 0).bijection.toFun i) := by
  by_cases before : i.val < a
  · let j : Fin (List.replicate a Wire.term).length := ⟨i.val,by simpa using before⟩
    have eq : ContractionTree.Graft.leftInsert (s := .term) (b := 1) P
        (CopyingMerge.net (a := 1) (b := 1) H H) 1 (.input j) = .input i := by
      rw [ContractionTree.Graft.left_input]; rfl
    rw [← eq]
    change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
    rw [ContractionTree.Graft.Join.left_port,CopyComponents.upstream_input]
    simp only [CopyContext.rotation,CopyContext.forwardIndex,before,↓reduceIte]
    rfl
  · have same : i.val = a := by have := i.isLt; simp only [List.length_replicate] at this; omega
    have eq : ContractionTree.Graft.rightInsert (s := .term) (b := 1) P
        (CopyingMerge.net (a := 1) (b := 1) H H) 1 (.input (0 : Fin 2)) = .input i := by
      have raw : ContractionTree.Graft.rightInsert (s := .term) (b := 1) P
          (CopyingMerge.net (a := 1) (b := 1) H H) 1 (.input (0 : Fin 2)) =
            .input ⟨a,by simp⟩ := by
        rw [ContractionTree.Graft.right_input]
        simp [ContractionTree.Graft.downstream,Port.map]
      rw [raw]
      exact congrArg Port.input (Fin.ext same.symm)
    rw [← eq]
    change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
    rw [ContractionTree.Graft.Join.right_port]
    have dup := CopyComponents.duplicate_input P H false
    change (CopyComponents.duplicate P H).ports (.input (0 : Fin 2)) = (CopyComponents.active P H).ports (.input 0) at dup
    rw [dup,CopyComponents.active_input]
    simp [CopyContext.rotation,CopyContext.forwardIndex,same]

theorem raw_output (i : Fin (environmentInterface k h).length) :
    (rawOccurrence P H).ports (.output i) = .output i := by
  have eq := ContractionTree.Graft.right_output (s := .term) (b := 1) P
    (CopyingMerge.net (a := 1) (b := 1) H H) (1 : Fin 2) i
  rw [← eq]
  change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
  rw [ContractionTree.Graft.Join.right_port,CopyComponents.duplicate_output]

noncomputable def occurrence :
    Occurrence (CopyContext.net (b := 0) P (CopyingMerge.net (a := 1) (b := 1) H H))
      (CopyComponents.target P H) :=
  (CopyingDouble.Symmetry.backward _ (CopyContext.rotation a 0)).comp (rawOccurrence P H)

theorem input (i : Fin (List.replicate (a+1) Wire.term).length) :
    (occurrence P H).ports (.input i) = .input i := by
  change (rawOccurrence P H).ports (.input ((CopyContext.rotation a 0).bijection.invFun i)) = _
  rw [raw_input,(CopyContext.rotation a 0).bijection.right_inv]

theorem output (i : Fin (environmentInterface k h).length) :
    (occurrence P H).ports (.output i) = .output i := raw_output P H i

/-- Every old residual-tree, both actual payload, and every distributor edge
is covered, so this normalization deletes or duplicates no graph component. -/
theorem cover : Function.Surjective (occurrence P H).edges := by
  cases d
  all_goals
    rintro ⟨outer,e⟩
    cases outer
    · rcases e with ⟨side,e⟩
      cases side
      · exact ⟨⟨true,⟨false,⟨false,e⟩⟩⟩,rfl⟩
      · rcases e with ⟨inside,e⟩
        cases inside
        · exact ⟨⟨false,e⟩,rfl⟩
        · exact ⟨⟨true,⟨false,⟨true,e⟩⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

noncomputable def iso :
    DeepIso (CopyContext.net (b := 0) P (CopyingMerge.net (a := 1) (b := 1) H H))
      (CopyComponents.target P H) :=
  (occurrence P H).iso_of_edge_surjective (input P H) (output P H) (cover P H)

/-- The normalization identifies the literal unchanged Figure 17 target. -/
noncomputable def afterIso (T : ContractionTree .term (a+1)) :
    DeepIso (CopyContext.net (b := 0) (CopyRule.residual T d) (CopyingMerge.net (a := 1) (b := 1) H H))
      (CopyRule.after T H) :=
  (iso (CopyRule.residual T d) H).trans
    (CopyingMerge.retainedIso H (Serial.net (CopyRule.residual T d) H)).symm

/-- One original compute step reaches the normalized enlarged pair. No
translation or operational rule is changed by this exact representation. -/
theorem rewrite (T : ContractionTree .term (a+1)) (copyable : Copyable H) :
    Combined.Rewrite (CopyRule.before T H) (.input ⟨0,by simp⟩)
      (CopyContext.net (b := 0) (CopyRule.residual T d) (CopyingMerge.net (a := 1) (b := 1) H H))
      (.input ⟨0,by simp⟩) := by
  exact (Combined.Rewrite.local (Combined.Local.copy T H copyable)).rename
    (DeepIso.refl _) (afterIso H T).symm

end Hypernets.Copying.Parametricity.CopyNormalization

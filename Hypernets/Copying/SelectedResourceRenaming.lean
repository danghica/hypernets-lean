import Hypernets.Copying.SelectedResourceShape

/-! Bijective renaming of the literal selected-resource translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SelectedResource
open Graph

def outputPermutation {n} (π : Bijection (Fin n) (Fin n)) : Bijection (Port Unit 1 n) (Port Unit 1 n) where
  toFun | .internal v => .internal v | .input i => .input i | .output j => .output (π.toFun j)
  invFun | .internal v => .internal v | .input i => .input i | .output j => .output (π.invFun j)
  left_inv v := by cases v <;> simp [π.left_inv]
  right_inv v := by cases v <;> simp [π.right_inv]

theorem source_permutation {n} (π : Bijection (Fin n) (Fin n)) (x : Fin n ⊕ Unit) :
    (source x).map (outputPermutation π).toFun = source ((π.sum (Bijection.refl Unit)).toFun x) := by
  cases x <;> rfl

theorem target_permutation {n} (π : Bijection (Fin n) (Fin n)) (i : Fin n) (x : Fin n ⊕ Unit) :
    (target i x).map (outputPermutation π).toFun = target (π.toFun i) ((π.sum (Bijection.refl Unit)).toFun x) := by
  cases x with
  | inr x => rfl
  | inl j =>
    have eq : π.toFun j = π.toFun i ↔ j = i := ⟨π.injective,congrArg π.toFun⟩
    simp only [target,Bijection.sum,Sum.elim_inl,Function.comp_apply,eq]
    split <;> rfl

theorem source_eq (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    (raw s d i).source (edgeAt s d i x) = (source x).map (ports s d i).invFun := by
  have h := congrArg (List.map (ports s d i).invFun) (source_at s d i x)
  simpa [List.map_map,Function.comp_def,(ports s d i).left_inv] using h

theorem target_eq (s : ShareSort) (d : Nat) {n} (i : Fin n) (x : Fin n ⊕ Unit) :
    (raw s d i).target (edgeAt s d i x) = (target i x).map (ports s d i).invFun := by
  have h := congrArg (List.map (ports s d i).invFun) (target_at s d i x)
  simpa [List.map_map,Function.comp_def,(ports s d i).left_inv] using h

/-- Actual port and edge bijections retain the selected contraction and every weakening. -/
def rawIso (s : ShareSort) (d : Nat) {n} (π : Bijection (Fin n) (Fin n)) (i : Fin n) :
    BoundaryIso (raw s d i) (raw s d (π.toFun i)) where
  ports := (ports s d i).trans ((outputPermutation π).trans (ports s d (π.toFun i)).symm)
  edges := (edges s d i).trans ((π.sum (Bijection.refl Unit)).trans (edges s d (π.toFun i)).symm)
  vertex_label v := by rw [vertex_label,vertex_label]
  input_iff v := by cases v <;> rfl
  output_iff v := by cases v <;> rfl
  edge_label e := by
    have hi := label_at s d i (edgeIndex s d i e)
    rw [edgeAt_index] at hi
    change LabelEquiv d _ ((raw s d (π.toFun i)).edgeLabel (edgeAt s d (π.toFun i) _))
    rw [hi,label_at]
    change LabelEquiv d (primitiveLabel d (label s (edgeIndex s d i e)))
      (primitiveLabel d (label s ((π.sum (Bijection.refl Unit)).toFun (edgeIndex s d i e))))
    cases edgeIndex s d i e <;> exact labelEquiv_refl _ _
  source e := by
    have hi := source_eq s d i (edgeIndex s d i e)
    rw [edgeAt_index] at hi
    change ((raw s d i).source e).map
      (fun v => (ports s d (π.toFun i)).invFun ((outputPermutation π).toFun ((ports s d i).toFun v))) =
        (raw s d (π.toFun i)).source (edgeAt s d (π.toFun i) ((π.sum (Bijection.refl Unit)).toFun (edgeIndex s d i e)))
    rw [hi,source_eq,← source_permutation π]
    simp only [List.map_map,Function.comp_def,(ports s d i).right_inv]
  target e := by
    have hi := target_eq s d i (edgeIndex s d i e)
    rw [edgeAt_index] at hi
    change ((raw s d i).target e).map
      (fun v => (ports s d (π.toFun i)).invFun ((outputPermutation π).toFun ((ports s d i).toFun v))) =
        (raw s d (π.toFun i)).target (edgeAt s d (π.toFun i) ((π.sum (Bijection.refl Unit)).toFun (edgeIndex s d i e)))
    rw [hi,target_eq,← target_permutation π i]
    simp only [List.map_map,Function.comp_def,(ports s d i).right_inv]
theorem rawIso_output (s : ShareSort) (d : Nat) {n}
    (π : Bijection (Fin n) (Fin n)) (i j : Fin n) :
    (rawIso s d π i).ports.toFun
      (.output ⟨j.val,Nat.lt_of_lt_of_eq j.isLt (output_length s i).symm⟩) =
      .output ⟨(π.toFun j).val,Nat.lt_of_lt_of_eq (π.toFun j).isLt (output_length s (π.toFun i)).symm⟩ := rfl

end Hypernets.Copying.SelectedResource

namespace Hypernets.Copying.BoundaryIso
open Graph

/-- Interface equality transport changes indices, never the graph or port order. -/
def castInterfaces {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) (f : BoundaryIso G H) :
    BoundaryIso (Translation.castInterfaces hi ho G) (Translation.castInterfaces hj hk H) := by
  cases hi; cases ho; cases hj; cases hk; exact f
theorem castInterfaces_output {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) (f : BoundaryIso G H)
    (a : Fin O.length) (b : Fin K.length) (h : f.ports.toFun (.output a) = .output b) :
    (castInterfaces hi ho hj hk f).ports.toFun (.output (Fin.cast (congrArg List.length ho) a)) =
      .output (Fin.cast (congrArg List.length hk) b) := by
  cases hi; cases ho; cases hj; cases hk; exact h
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.Translation
open Graph
/-- Bijective renaming for Figure 16's original selected-resource clause. -/
def selectedResource_rename (d : Nat) (s : ShareSort) {n}
    (π : Bijection (Fin n) (Fin n)) (i : Fin n) :
    BoundaryIso (selectedResource d s i) (selectedResource d s (π.toFun i)) := by
  unfold selectedResource
  exact BoundaryIso.castInterfaces _ _ _ _ (SelectedResource.rawIso s d π i)
/-- The public selected-resource isomorphism implements the requested permutation exactly. -/
theorem selectedResource_rename_output (d : Nat) (s : ShareSort) {n}
    (π : Bijection (Fin n) (Fin n)) (i j : Fin n) :
    (selectedResource_rename d s π i).ports.toFun (.output ⟨j.val,by simpa using j.isLt⟩) =
      .output ⟨(π.toFun j).val,by simpa using (π.toFun j).isLt⟩ := by
  unfold selectedResource_rename
  exact BoundaryIso.castInterfaces_output _ _ _ _ (SelectedResource.rawIso s d π i) _ _
    (SelectedResource.rawIso_output s d π i j)
end Hypernets.Copying.Translation

import Hypernets.Copying.BoundarySafety

/-! A concrete instantiation of compatible gluing on the unchanged distributors,
including many-use forests followed by single-use forests. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph
/-- Input action survives the interface equalities used by the original translation. -/
theorem castInterfaces_input {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) (f : BoundaryIso G H)
    (a : Fin I.length) (b : Fin J.length) (h : f.ports.toFun (.input a) = .input b) :
    (castInterfaces hi ho hj hk f).ports.toFun (.input (Fin.cast (congrArg List.length hi) a)) =
      .input (Fin.cast (congrArg List.length hj) b) := by
  cases hi; cases ho; cases hj; cases hk; exact h
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.Distributor
open Graph
/-- D(k,1) with its input length equality exposed; all tree edges are retained. -/
def single (s : ShareSort) (k d : Nat) : Hypernet d (List.replicate k s.wire) (List.replicate k s.wire) :=
  Translation.castInterfaces (by rw [Nat.mul_one]) rfl (atDepth s k 1 d)

def singleIso (s : ShareSort) {k} (d : Nat) (π : Bijection (Fin k) (Fin k)) :
    BoundaryIso (single s k d) (single s k d) :=
  BoundaryIso.castInterfaces _ _ _ _ (boundaryIso s 1 d π)

theorem singleIso_input (s : ShareSort) {k} (d : Nat) (π : Bijection (Fin k) (Fin k)) (i : Fin k) :
    (singleIso s d π).ports.toFun (.input ⟨i.val,by simpa using i.isLt⟩) =
      .input ⟨(π.toFun i).val,by simpa using (π.toFun i).isLt⟩ := by
  have h := BoundaryIso.castInterfaces_input (G := atDepth s k 1 d) (H := atDepth s k 1 d)
    (show List.replicate (k*1) s.wire = List.replicate k s.wire by rw [Nat.mul_one]) rfl
    (show List.replicate (k*1) s.wire = List.replicate k s.wire by rw [Nat.mul_one]) rfl
    (boundaryIso s 1 d π) (inputIndex s ⟨i,⟨0,by simp⟩⟩) (inputIndex s ⟨π.toFun i,⟨0,by simp⟩⟩)
    (resourcePorts_input (m := 1) s π i ⟨0,by simp⟩)
  exact h

theorem singleIso_output (s : ShareSort) {k} (d : Nat) (π : Bijection (Fin k) (Fin k)) (i : Fin k) :
    (singleIso s d π).ports.toFun (.output ⟨i.val,by simpa using i.isLt⟩) =
      .output ⟨(π.toFun i).val,by simpa using (π.toFun i).isLt⟩ :=
  BoundaryIso.castInterfaces_output _ _ _ _ (boundaryIso s 1 d π) _ _ (resourcePorts_output s π i)

/-- The extracted output-index bijection is the advertised resource action. -/
theorem outputIndex_eq (s : ShareSort) {k} (m d : Nat) (π : Bijection (Fin k) (Fin k))
    (j : Fin (List.replicate k s.wire).length) :
    (boundaryIso s m d π).outputs.toFun j =
      ⟨(π.toFun ⟨j.val,by simpa using j.isLt⟩).val,by simp⟩ := by
  apply Port.output.inj (Internal := (atDepth s k m d).Internal) (inputs := (List.replicate (k*m) s.wire).length)
  change Port.output ((boundaryIso s m d π).outputMap j) = _
  rw [← BoundaryIso.map_output]
  exact resourcePorts_output s π ⟨j.val,by simpa using j.isLt⟩

/-- Single-use input indices carry the same action, with no use-block offset. -/
theorem singleInputIndex_eq (s : ShareSort) {k} (d : Nat) (π : Bijection (Fin k) (Fin k))
    (j : Fin (List.replicate k s.wire).length) :
    (singleIso s d π).inputs.toFun j =
      ⟨(π.toFun ⟨j.val,by simpa using j.isLt⟩).val,by simp⟩ := by
  apply Port.input.inj (Internal := (single s k d).Internal) (outputs := (List.replicate k s.wire).length)
  change Port.input ((singleIso s d π).inputMap j) = _
  rw [← BoundaryIso.map_input]
  exact singleIso_input s d π ⟨j.val,by simpa using j.isLt⟩

/-- Matching the same resource permutation on both actual forests satisfies gluing. -/
theorem single_compatible (s : ShareSort) {k} (m d : Nat) (π : Bijection (Fin k) (Fin k)) :
    BoundarySerial.Compatible (boundaryIso s m d π) (singleIso s d π) := by
  intro j
  rw [outputIndex_eq,singleInputIndex_eq]

/-- Unbounded resource counts and use counts: equivariance of a genuine serial
composition, retaining the extra single-use distributors required by Figure 16. -/
def serial_singleIso (s : ShareSort) {k} (m d : Nat) (π : Bijection (Fin k) (Fin k)) :
    BoundaryIso (Serial.net (atDepth s k m d) (single s k d))
      (Serial.net (atDepth s k m d) (single s k d)) :=
  BoundarySerial.iso (boundaryIso s m d π) (singleIso s d π) (single_compatible s m d π)

/-- Conversely, gluing these forests forces the two resource permutations to coincide. -/
theorem single_compatible_iff (s : ShareSort) {k} (m d : Nat)
    (π τ : Bijection (Fin k) (Fin k)) :
    BoundarySerial.Compatible (boundaryIso s m d π) (singleIso s d τ) ↔ π.toFun = τ.toFun := by
  constructor
  · intro h
    funext i
    have eq := h ⟨i.val,by simpa using i.isLt⟩
    rw [outputIndex_eq,singleInputIndex_eq] at eq
    exact Fin.ext (congrArg (fun j : Fin (List.replicate k s.wire).length => j.val) eq)
  · intro eq j
    rw [outputIndex_eq,singleInputIndex_eq,eq]
end Hypernets.Copying.Distributor

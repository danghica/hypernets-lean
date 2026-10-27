import Hypernets.Copying.PermutationExecution

/-! Move external permutations through the original serial and tensor assemblies. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace TypedPermutation

theorem append_symm {I O : List Wire} (p : TypedPermutation I) (q : TypedPermutation O) :
    (p.append q).symm = p.symm.append q.symm := rfl
theorem symm_refl (O : List Wire) : (refl O).symm = refl O := rfl
end TypedPermutation
namespace InterfacePermutation

/-- Permuting the last component's outputs is the same external action after serial gluing. -/
def serial {d I J O} (G : Hypernet d I J) (H : Hypernet d J O) (p : TypedPermutation O) :
    DeepIso (Serial.net G (net H p)) (net (Serial.net G H) p) := by
  let f := BoundaryIso.refl G
  let g := iso H p
  have compatible : BoundarySerial.Compatible f g := fun _ => rfl
  exact (realize (BoundarySerial.iso f g compatible) p
    (fun i => by
      have eq := BoundarySerial.iso_input f g compatible i
      rw [BoundaryIso.map_input] at eq
      exact Port.input.inj eq)
    (fun i => by
      have eq := BoundarySerial.iso_output f g compatible i
      rw [BoundaryIso.map_output] at eq
      exact Port.output.inj eq)).symm

/-- Two independent component actions give exactly the concatenated output action. -/
def tensor {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K)
    (p : TypedPermutation O) (q : TypedPermutation K) :
    DeepIso (Net.Tensor.net (net G p) (net H q)) (net (Net.Tensor.net G H) (p.append q)) := by
  let f := iso G p
  let g := iso H q
  apply DeepIso.symm
  apply realize (f.tensor g) (p.append q)
  · intro i
    apply Port.input.inj (Internal := (Net.Tensor.net (net G p) (net H q)).Internal) (outputs := (O++K).length)
    change Port.input ((f.tensor g).inputMap i) = _
    rw [← BoundaryIso.map_input]
    have eq := Net.Tensor.join_split I J i
    generalize hsplit : Net.Tensor.split I J i = x at eq
    rcases x with ⟨b,j⟩
    rw [← eq]
    cases b
    · exact f.tensor_input_left g j
    · exact f.tensor_input_right g j
  · intro i
    apply Port.output.inj (Internal := (Net.Tensor.net (net G p) (net H q)).Internal) (inputs := (I++J).length)
    change Port.output ((f.tensor g).outputMap i) = _
    rw [← BoundaryIso.map_output]
    have eq := Net.Tensor.join_split O K i
    generalize hsplit : Net.Tensor.split O K i = x at eq
    rcases x with ⟨b,j⟩
    rw [← eq]
    cases b
    · rw [TypedPermutation.append_left]; exact f.tensor_output_left g j
    · rw [TypedPermutation.append_right]; exact f.tensor_output_right g j

/-- The identity output action changes no ordered graph, up to representation. -/
def reflIso {d I O} (G : Hypernet d I O) : DeepIso G (net G (.refl O)) :=
  (iso G (.refl O)).toDeepIso (fun _ => rfl) (fun _ => rfl)

/-- The unaffected tensor component remains literally the same graph. -/
def tensor_left {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K)
    (p : TypedPermutation O) :
    DeepIso (Net.Tensor.net (net G p) H) (net (Net.Tensor.net G H) (p.append (.refl K))) :=
  (Application.tensor_congr (DeepIso.refl _) (reflIso H)).trans (tensor G H p (.refl K))
end InterfacePermutation
end Hypernets.Copying

import Hypernets.Copying.TensorBoundaryActions

/-! Synchronous boundary actions of private-output and closed families.
The left outputs track precisely the common external input permutation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph

theorem trans_inputs {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K} {F : Hypernet d U V}
    (f : BoundaryIso G H) (g : BoundaryIso H F) (i : Fin I.length) :
    (f.trans g).inputs.toFun i = g.inputs.toFun (f.inputs.toFun i) := by
  apply Port.input.inj (Internal := F.Internal) (outputs := V.length)
  dsimp only [inputs]
  rw [← map_input,← map_input]
  change g.ports.toFun (f.ports.toFun (.input i)) = g.ports.toFun (.input (f.inputs.toFun i))
  rw [f.map_input]
  rfl

theorem trans_outputs {d I O J K U V} {G : Hypernet d I O} {H : Hypernet d J K} {F : Hypernet d U V}
    (f : BoundaryIso G H) (g : BoundaryIso H F) (i : Fin O.length) :
    (f.trans g).outputs.toFun i = g.outputs.toFun (f.outputs.toFun i) := by
  apply Port.output.inj (Internal := F.Internal) (inputs := U.length)
  dsimp only [outputs]
  rw [← map_output,← map_output]
  change g.ports.toFun (f.ports.toFun (.output i)) = g.ports.toFun (.output (f.outputs.toFun i))
  rw [f.map_output]
  rfl

/-- Shared boundary action, including the left private-output attachment. -/
def Synchronous {d I J} {L : Hypernet d I I} {R : Hypernet d I []}
    {L' : Hypernet d J J} {R' : Hypernet d J []}
    (f : BoundaryIso L L') (g : BoundaryIso R R') : Prop :=
  (∀ i, f.inputs.toFun i = g.inputs.toFun i) ∧ (∀ i, f.outputs.toFun i = f.inputs.toFun i)

theorem synchronous_refl {d I} (L : Hypernet d I I) (R : Hypernet d I []) :
    Synchronous (refl L) (refl R) := ⟨fun _ => rfl,fun _ => rfl⟩

/-- Composing synchronized family changes retains both required boundary
agreements; no graph equality or semantic closure is assumed. -/
theorem Synchronous.trans {d I J K} {L : Hypernet d I I} {R : Hypernet d I []}
    {L' : Hypernet d J J} {R' : Hypernet d J []} {L'' : Hypernet d K K} {R'' : Hypernet d K []}
    {f : BoundaryIso L L'} {g : BoundaryIso R R'} {f' : BoundaryIso L' L''} {g' : BoundaryIso R' R''}
    (h : Synchronous f g) (h' : Synchronous f' g') : Synchronous (f.trans f') (g.trans g') := by
  constructor
  · intro i; rw [trans_inputs,trans_inputs,h.1,h'.1]
  · intro i; rw [trans_outputs,trans_inputs,h.2,h'.2]

/-- Independent synchronized families can be assembled in the literal
tensor, preserving the same complete input/private-output order. -/
theorem Synchronous.tensor {d I J K U} {L : Hypernet d I I} {R : Hypernet d I []}
    {L' : Hypernet d J J} {R' : Hypernet d J []} {A : Hypernet d K K} {B : Hypernet d K []}
    {A' : Hypernet d U U} {B' : Hypernet d U []}
    {f : BoundaryIso L L'} {g : BoundaryIso R R'} {f' : BoundaryIso A A'} {g' : BoundaryIso B B'}
    (h : Synchronous f g) (h' : Synchronous f' g') : Synchronous (f.tensor f') (g.tensor g') := by
  constructor
  · intro i
    let p := Net.Tensor.split I K i
    have eq := Net.Tensor.join_split I K i
    change Net.Tensor.join I K p = i at eq
    obtain ⟨side,j⟩ := p
    cases side
    · apply Port.input.inj (Internal := (Net.Tensor.net L' A').Internal) (outputs := (J++U).length)
      dsimp only [inputs]
      rw [← (f.tensor f').map_input,← eq,BoundaryIso.tensor_input_left]
      have other := (g.tensor g').map_input (Net.Tensor.join I K ⟨false,j⟩)
      rw [BoundaryIso.tensor_input_left] at other
      have indices := Port.input.inj other
      rw [← indices,h.1]
    · apply Port.input.inj (Internal := (Net.Tensor.net L' A').Internal) (outputs := (J++U).length)
      dsimp only [inputs]
      rw [← (f.tensor f').map_input,← eq,BoundaryIso.tensor_input_right]
      have other := (g.tensor g').map_input (Net.Tensor.join I K ⟨true,j⟩)
      rw [BoundaryIso.tensor_input_right] at other
      have indices := Port.input.inj other
      rw [← indices,h'.1]
  · intro i
    let p := Net.Tensor.split I K i
    have eq := Net.Tensor.join_split I K i
    change Net.Tensor.join I K p = i at eq
    obtain ⟨side,j⟩ := p
    cases side
    · have out := (f.tensor f').map_output (Net.Tensor.join I K ⟨false,j⟩)
      have inp := (f.tensor f').map_input (Net.Tensor.join I K ⟨false,j⟩)
      rw [tensor_output_left] at out
      rw [tensor_input_left] at inp
      dsimp only [outputs,inputs]
      rw [← eq,← Port.output.inj out,← Port.input.inj inp,h.2]
    · have out := (f.tensor f').map_output (Net.Tensor.join I K ⟨true,j⟩)
      have inp := (f.tensor f').map_input (Net.Tensor.join I K ⟨true,j⟩)
      rw [tensor_output_right] at out
      rw [tensor_input_right] at inp
      dsimp only [outputs,inputs]
      rw [← eq,← Port.output.inj out,← Port.input.inj inp,h'.2]

end Hypernets.Copying.BoundaryIso

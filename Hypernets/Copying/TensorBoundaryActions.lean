import Hypernets.Copying.EnvironmentPermutation

/-! Exact block actions for ordered tensor boundaries. -/
namespace Hypernets.Copying.BoundaryIso
open Graph
variable {d I O J K U V W X} {G : Hypernet d I O} {H : Hypernet d J K}
    {G' : Hypernet d U V} {H' : Hypernet d W X} (f : BoundaryIso G G') (g : BoundaryIso H H')

theorem tensor_input_left (i : Fin I.length) :
    (f.tensor g).ports.toFun (.input (Net.Tensor.join I J ⟨false,i⟩)) =
      .input (Net.Tensor.join U W ⟨false,f.inputs.toFun i⟩) := by
  have h := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H') (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary I O J K) (Net.Tensor.boundary U V W X) false (.input i)
  change (f.tensor g).ports.toFun (.input (Net.Tensor.join I J ⟨false,i⟩)) =
    Net.Parallel.embed (Net.Tensor.family G' H') (Net.Tensor.boundary U V W X) false (f.ports.toFun (.input i)) at h
  rw [f.map_input] at h
  exact h

theorem tensor_input_right (i : Fin J.length) :
    (f.tensor g).ports.toFun (.input (Net.Tensor.join I J ⟨true,i⟩)) =
      .input (Net.Tensor.join U W ⟨true,g.inputs.toFun i⟩) := by
  have h := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H') (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary I O J K) (Net.Tensor.boundary U V W X) true (.input i)
  change (f.tensor g).ports.toFun (.input (Net.Tensor.join I J ⟨true,i⟩)) =
    Net.Parallel.embed (Net.Tensor.family G' H') (Net.Tensor.boundary U V W X) true (g.ports.toFun (.input i)) at h
  rw [g.map_input] at h
  exact h

theorem tensor_output_left (i : Fin O.length) :
    (f.tensor g).ports.toFun (.output (Net.Tensor.join O K ⟨false,i⟩)) =
      .output (Net.Tensor.join V X ⟨false,f.outputs.toFun i⟩) := by
  have h := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H') (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary I O J K) (Net.Tensor.boundary U V W X) false (.output i)
  change (f.tensor g).ports.toFun (.output (Net.Tensor.join O K ⟨false,i⟩)) =
    Net.Parallel.embed (Net.Tensor.family G' H') (Net.Tensor.boundary U V W X) false (f.ports.toFun (.output i)) at h
  rw [f.map_output] at h
  exact h

theorem tensor_output_right (i : Fin K.length) :
    (f.tensor g).ports.toFun (.output (Net.Tensor.join O K ⟨true,i⟩)) =
      .output (Net.Tensor.join V X ⟨true,g.outputs.toFun i⟩) := by
  have h := BoundaryParallel.embed (G := Net.Tensor.family G H) (H := Net.Tensor.family G' H') (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary I O J K) (Net.Tensor.boundary U V W X) true (.output i)
  change (f.tensor g).ports.toFun (.output (Net.Tensor.join O K ⟨true,i⟩)) =
    Net.Parallel.embed (Net.Tensor.family G' H') (Net.Tensor.boundary U V W X) true (g.ports.toFun (.output i)) at h
  rw [g.map_output] at h
  exact h
end Hypernets.Copying.BoundaryIso

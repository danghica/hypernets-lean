import Hypernets.Copying.BoundaryParallel
import Hypernets.Copying.BoxPullWeakeningReverseBeta

/-! Tensor boundary actions retain the actual port maps of each complete
component, including internal ports and unequal interface presentations. -/
namespace Hypernets.Copying.BoundaryIso
open Graph
variable {d I O J K U V W X} {A : Hypernet d I O} {B : Hypernet d J K}
    {A' : Hypernet d U V} {B' : Hypernet d W X} (f : BoundaryIso A A') (g : BoundaryIso B B')

theorem tensor_left_port (v : A.Vertex) :
    (f.tensor g).ports.toFun ((BoxPullWeakening.ReverseComponents.tensorLeft A B).ports v) =
      (BoxPullWeakening.ReverseComponents.tensorLeft A' B').ports (f.ports.toFun v) :=
  BoundaryParallel.embed (G := Net.Tensor.family A B) (H := Net.Tensor.family A' B')
    (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary _ _ _ _) (Net.Tensor.boundary _ _ _ _) false v

theorem tensor_right_port (v : B.Vertex) :
    (f.tensor g).ports.toFun ((BoxPullWeakening.ReverseComponents.tensorRight A B).ports v) =
      (BoxPullWeakening.ReverseComponents.tensorRight A' B').ports (g.ports.toFun v) :=
  BoundaryParallel.embed (G := Net.Tensor.family A B) (H := Net.Tensor.family A' B')
    (fun b => match b with | false => f | true => g)
    (Net.Tensor.boundary _ _ _ _) (Net.Tensor.boundary _ _ _ _) true v
end Hypernets.Copying.BoundaryIso

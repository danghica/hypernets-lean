import Hypernets.Copying.CopyingDoubleFrame
import Hypernets.Copying.FillingAssembly

/-! A common normal presentation with three identical payloads, the full
remaining contraction tree, and actual two-layer canonical resource rows. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble
open Graph

namespace Frame
variable {d n k h}

def row (i : Resource k h) (swapped : Bool) :
    Hypernet d (List.replicate 3 (environmentInterface k h)[i]) [(environmentInterface k h)[i]] :=
  (if swapped then CopyingInputPermutation.net (Row.graph (sort k h i) d) (Row.exchange (sort k h i))
    else Row.graph (sort k h i) d).reboundary
      (congrArg (List.replicate 3) (sort_wire k h i)) (congrArg List.singleton (sort_wire k h i))

noncomputable def family (H : Hypernet d [.term] (environmentInterface k h))
    (R : ContractionTree .term n) (swapped : Bool) (e : (graph n k h d).Edge) :
    Hypernet d ((alphabet d).signature.input ((graph n k h d).edgeLabel e))
      ((alphabet d).signature.output ((graph n k h d).edgeLabel e)) := by
  cases d <;> rcases e with b | (j | i)
  all_goals first | exact H | exact R.atDepth _ | exact row i swapped

/-- This is a finite expansion of an explicit three-payload frame. -/
noncomputable def normal (H : Hypernet d [.term] (environmentInterface k h))
    (R : ContractionTree .term n) (swapped : Bool) :
    Hypernet d (List.replicate (n+2) .term) (environmentInterface k h) :=
  (graph n k h d).expand (family H R swapped)

/-- Interchanging two uses changes only independently proved sharing-tree
components; every payload is literally retained in the same ordered slot. -/
noncomputable def witness (H : Hypernet d [.term] (environmentInterface k h))
    (free : FocusFree H) (R S : ContractionTree .term n) :
    FillingWitness SharingTreeAlgebra.template (normal H R false) (normal H S true) := by
  apply FillingWitness.expand
  intro e
  cases d <;> rcases e with b | (j | i)
  all_goals first
    | exact FillingWitness.refl H free
    | exact FillingWitness.of_rel 0 (SharingTreeAlgebra.literal R S _)
    | exact (Row.witness (sort k h i) _).reboundary
        (congrArg (List.replicate 3) (sort_wire k h i)) (congrArg List.singleton (sort_wire k h i))
end Frame
end Hypernets.Copying.CopyingDouble

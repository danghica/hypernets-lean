import Hypernets.Copying.ParametricityPrivateReindex
import Hypernets.Copying.ParametricitySelectedIsolated

/-! Arithmetic interface presentations do not alter the actual original
private sharing tree. The pulled-back tree supplies a synchronized complete
source presentation for the arbitrary selected family-copy diagram. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateReindex
open Graph

/-- The exact original private tree admits a pulled-back isolated source
for any provably equal arity presentation. Its full external action is the
recorded action of the original family isomorphism. -/
theorem presentation {d m n N}
    (count : N = m+n)
    {L : Hypernet (d+2) (List.replicate N .term) (List.replicate N .term)}
    (f : BoundaryIso L (leftFamily d m n)) (C : ContractionTree .term (m+n)) :
    ∃ D : ContractionTree .term N,
      ∃ g : BoundaryIso (Serial.net (Serial.net L (D.atDepth (d+2))) (privateCell (d+2))) (left d C),
        ∀ i, g.inputs.toFun i = f.inputs.toFun i := by
  cases count
  exact ⟨tree f C,leftIso f C,leftIso_input f C⟩

end Hypernets.Copying.Parametricity.PrivateReindex

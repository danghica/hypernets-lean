import Hypernets.Copying.FiniteGraphCertificate
import Hypernets.Copying.ParametricityEquivalence
import Hypernets.Copying.SharingTreeAlgebra

/-! Literal intermediate graphs for the right-hand normalization. Original
translation clauses are retained until their sharing structure is certified. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.Result
open Graph

def callbackTerm : Term 1 0 := .app (.var 0) (.const .unit)
def bodyTerm : Term 1 0 := .app (.lam (.const (.nat 1))) callbackTerm

def mixed : Hypernet 1 [.term] [.term] :=
  Translation.application (BoxPullWeakening.extend (k := 0) (h := 0) (Parametricity.smallRight 0) .term)
    (Translation.padTo 1 (by decide) (Translation.term callbackTerm))

/-- All five weakenings and all five contractions retained by the two actual
application clauses, in their original ordered tree. -/
def sharing : Hypernet 1 [.term] [.term] :=
  Serial.net (Net.Tensor.net (primitiveNet 1 (.weakening .term))
    (Serial.net (Net.Tensor.net (CanonicalTree.atDepth .term 1 1)
      (primitiveNet 1 (.weakening .term))) (CanonicalTree.atDepth .term 2 1)))
    (CanonicalTree.atDepth .term 2 1)

def schematic (T : Hypernet 1 [.term] [.term]) : Hypernet 1 [.term] [.term] :=
  Serial.net (primitiveNet 1 (.operation .app))
    (Net.Tensor.net (Parametricity.smallRight 0)
      (Serial.net (primitiveNet 1 (.operation .app))
        (Net.Tensor.net T (primitiveNet 1 (.operation (.const .unit))))))

end Hypernets.Copying.Proposition12_2.Result

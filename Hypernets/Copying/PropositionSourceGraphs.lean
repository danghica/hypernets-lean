import Hypernets.Copying.PropositionStructuralCalculation
import Hypernets.Copying.PropositionResultGraphs
import Hypernets.Copying.PropositionAllocationGeometry

/-! Literal source-normalization graphs. The original terms and translation
remain unchanged; each auxiliary graph records a structural intermediate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2.Source
open Graph

def readTerm : Term 3 0 := .unary .deref (.var 2)
def weak (d : Nat) := primitiveNet d (.weakening .term)
def use (d : Nat) := CanonicalTree.atDepth .term 1 d
def unusedRow (d : Nat) := Serial.net (weak d) (use d)
def usedRow (d : Nat) := Serial.net (use d) (use d)

def readParts (W V : Hypernet 0 [] [.term]) (T : Hypernet 0 [.term] [.term]) :
    Hypernet 0 [.term] (environmentInterface 3 0) :=
  Net.Tensor.net (Net.Tensor.net W V)
    (Serial.net (primitiveNet 0 (.operation (.unary .deref))) T)

def readFactored := readParts (unusedRow 0) (unusedRow 0) (usedRow 0)
def readReduced := readParts (weak 0) (weak 0) (use 0)

/-- The outer two free outputs swap, while the first bound output is fixed. -/
def swapPair : BoxPermutation.Pair 1 2 0 := BoxPermutation.pair 1 Parametricity.boundFirst

/-- An unused free output is put before x, without moving the bound output. -/
def beforeX {d} (G : Hypernet d [.term] (environmentInterface 2 0)) :
    Hypernet d [.term] (environmentInterface 3 0) :=
  InterfacePermutation.net (BoxPullWeakening.body (n := 1) (k := 1) (h := 0) G .term) swapPair.body.symm

/-- The canonical one-use row on x is still inside the box. -/
def insideUse {d} (G : Hypernet d [.term] (environmentInterface 2 0)) :
    Hypernet d [.term] (environmentInterface 2 0) :=
  BoxPullContraction.body (n := 1) (k := 0) (h := 0) .term (beforeX G)

def readUsed : Hypernet 0 [.term] (environmentInterface 2 0) := insideUse (Parametricity.readBody 0)

def smallUsed := lambdaPayload (k := 1) (h := 0) readUsed

def innerReduced := Translation.abstraction readReduced

/-- BPullC's literal right endpoint, before serial reassociation. -/
def pullRight {d} (G : Hypernet d [.term] (environmentInterface 2 0)) :=
  Serial.net (primitiveNet (d+1) (.operation .lam))
    (BoxPullContraction.right (n := 1) (k := 0) (h := 0) .term (beforeX G))

/-- Two free outputs of the box feed the actual ordered contraction. -/
def contractBox {d} (G : Hypernet d [.term] (environmentInterface 3 0)) :=
  Serial.net (lambdaPayload (k := 2) (h := 0) G) (primitiveNet (d+1) (.contraction .term))

def permutedBox {d} (G : Hypernet d [.term] (environmentInterface 2 0)) :=
  Serial.net (primitiveNet (d+1) (.operation .lam))
    (InterfacePermutation.net (BoxPullWeakening.left (n := 1) (k := 1) (h := 0) G .term) swapPair.outer.symm)

def outsideWeak {d} (G : Hypernet d [.term] (environmentInterface 2 0)) :=
  Serial.net (primitiveNet (d+1) (.operation .lam))
    (InterfacePermutation.net (BoxPullWeakening.right (n := 1) (k := 1) (h := 0) G .term) swapPair.outer.symm)

/-- The translation's two outer single-use rows remain attached. -/
def innerAfterWeak := Serial.net (outsideWeak readUsed) (Translation.singleUse 1 2 0)

def innerNormal := Serial.net
  (Net.Tensor.net (weak 1) (Serial.net (Parametricity.smallLeft 0) (use 1)))
  (Translation.singleUse 1 2 0)

/-- The exact callback in the environment f,x. -/
def callbackTerm : Term 2 0 := .app (.var 0) (.const .unit)
def sequenceTerm : Term 2 0 := .app (.lam readTerm) callbackTerm

def sequenceNormal := Translation.application innerNormal
  (Translation.padTo 1 (by decide) (Translation.term callbackTerm))

/-- The complete f and x sharing components of the translated sequence. -/
def callbackTree := Serial.net
  (Net.Tensor.net (unusedRow 1)
    (Serial.net (Net.Tensor.net (use 1) (weak 1)) (CanonicalTree.atDepth .term 2 1)))
  (CanonicalTree.atDepth .term 2 1)
def privateTree := Serial.net
  (Net.Tensor.net (usedRow 1)
    (Serial.net (Net.Tensor.net (weak 1) (weak 1)) (CanonicalTree.atDepth .term 2 1)))
  (CanonicalTree.atDepth .term 2 1)

def sequenceParts (F X : Hypernet 1 [.term] [.term]) : Hypernet 1 [.term] (environmentInterface 2 0) :=
  InterfacePermutation.net
    (Serial.net (primitiveNet 1 (.operation .app))
      (Net.Tensor.net (Serial.net (Parametricity.smallLeft 0) X)
        (Serial.net (primitiveNet 1 (.operation .app))
          (Net.Tensor.net F (primitiveNet 1 (.operation (.const .unit))))))) Parametricity.boundFirst

def bodyNormal := Serial.net (Parametricity.largeLeft 0) (usedRow 2)

end Hypernets.Copying.Proposition12_2.Source

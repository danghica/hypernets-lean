import Hypernets.Copying.BoxPullWeakeningOpening
import Hypernets.Copying.InterfacePermutation
import Hypernets.Copying.Allocation
import Hypernets.Copying.MinimalContractionSpine

/-! The literal schematic graphs of Figure 20. The two abstraction families
are retained separately and in their displayed order. The private reference
is shared through an arbitrary TERM contraction tree, followed by the single
instance, canonical ATOM D₁,₁, store, and numeral 1. These graphs are not a
replacement definition of the inductive term translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph

/-- The ignored w is the first bound output; dereferencing reaches the sole
free variable x, exactly as in the smaller left abstraction of Figure 20. -/
def readBody (d : Nat) : Hypernet d [.term] (environmentInterface 2 0) :=
  BoxPullWeakening.adjoin (A := []) (B := [.term])
    (primitiveNet d (.operation (.unary .deref))) .term

/-- The smaller right abstraction ignores w and returns literal numeral 1. -/
def oneBody (d : Nat) : Hypernet d [.term] (environmentInterface 1 0) :=
  BoxPullWeakening.adjoin (A := []) (B := [])
    (primitiveNet d (.operation (.const (.nat 1)))) .term

def smallLeft (d : Nat) : Hypernet (d+1) [.term] [.term] := lambdaPayload (readBody d)
def smallRight (d : Nat) : Hypernet (d+1) [.term] [] := lambdaPayload (oneBody d)

/-- The callback f() retains the original displayed single-use term
contraction tree D₁,₁ and the literal unit edge. -/
def callback (d : Nat) : Hypernet d [.term] [.term] :=
  Serial.net (primitiveNet d (.operation .app))
    (Net.Tensor.net (CanonicalTree.atDepth .term 1 d)
      (primitiveNet d (.operation (.const .unit))))

/-- Swap only the two equal-typed output positions, making f the bound
output and x the free output of the larger left abstraction. -/
def boundFirst : TypedPermutation [.term,.term] where
  bijection := ⟨Fin.rev,Fin.rev,Fin.rev_rev,Fin.rev_rev⟩
  typed i := by
    change (List.replicate 2 Wire.term)[i.rev.val] = (List.replicate 2 Wire.term)[i.val]
    simp only [List.getElem_replicate]

def callReadBody (d : Nat) : Hypernet (d+1) [.term] (environmentInterface 2 0) :=
  InterfacePermutation.net
    (Serial.net (primitiveNet (d+1) (.operation .app))
      (Net.Tensor.net (smallLeft d) (callback (d+1)))) boundFirst

def callOneBody (d : Nat) : Hypernet (d+1) [.term] (environmentInterface 1 0) :=
  Serial.net (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (smallRight d) (callback (d+1)))

def largeLeft (d : Nat) : Hypernet (d+2) [.term] [.term] := lambdaPayload (callReadBody d)
def largeRight (d : Nat) : Hypernet (d+2) [.term] [] := lambdaPayload (callOneBody d)

/-- Ordered disjoint copies, including zero copies. No identity edge is
inserted: the zero case is the actual empty hypernet. -/
def copies {d k} (G : Hypernet d [.term] (List.replicate k .term)) :
    (m : Nat) → Hypernet d (List.replicate m .term) (List.replicate (k*m) .term)
  | 0 => Net.empty (alphabet d).signature
  | m+1 => (Net.Tensor.net G (copies G m)).reboundary
      (by simp [List.replicate_succ])
      (by rw [List.replicate_append_replicate]; simp [Nat.mul_succ,Nat.add_comm])

/-- m₁ larger abstractions precede m₂ smaller abstractions; all free x
outputs are kept, in that same order, for the private sharing tree. -/
def leftFamily (d m₁ m₂ : Nat) :
    Hypernet (d+2) (List.replicate (m₁+m₂) .term) (List.replicate (m₁+m₂) .term) :=
  (Net.Tensor.net (copies (k := 1) (largeLeft d) m₁)
    (copies (k := 1) (smallLeft (d+1)) m₂)).reboundary
      (by rw [List.replicate_append_replicate])
      (by simp only [Nat.one_mul,List.replicate_append_replicate])

def rightFamily (d m₁ m₂ : Nat) :
    Hypernet (d+2) (List.replicate (m₁+m₂) .term) [] :=
  (Net.Tensor.net (copies (k := 0) (largeRight d) m₁)
    (copies (k := 0) (smallRight (d+1)) m₂)).reboundary
      (by rw [List.replicate_append_replicate]) (by simp)

/-- The private reference contains the canonical atom D₁,₁; it is not
replaced by a direct wire or a simplified store encoding. -/
def privateCell (d : Nat) : Hypernet d [.term] [] :=
  Allocation.after (primitiveNet d (.operation (.const (.nat 1))))

/-- The entire finite family alone owns every input of C and the unique
instance feeding its private store. There is no free resource output. -/
def left {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
    Hypernet (d+2) (List.replicate (m₁+m₂) .term) [] :=
  Serial.net (Serial.net (leftFamily d m₁ m₂) (C.atDepth (d+2))) (privateCell (d+2))

def right (d m₁ m₂ : Nat) : Hypernet (d+2) (List.replicate (m₁+m₂) .term) [] :=
  rightFamily d m₁ m₂

end Hypernets.Copying.Parametricity

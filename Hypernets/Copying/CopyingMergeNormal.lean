import Hypernets.Copying.CopyingMergeInputs
import Hypernets.Copying.CopyingMerge

/-! A common three-branch presentation for nested resource merging. The three
original branches remain fixed; only their actual six-edge resource rows vary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingMerge.Frame
open Graph
variable {d N k h : Nat} {arity : Fin 3 → Nat}
    (inputs : Bijection (Σ b : Fin 3, Fin (arity b)) (Fin N))
    (branches : ∀ b, Hypernet d (List.replicate (arity b) .term) (environmentInterface k h))

def row (i : Resource k h) (associateRight : Bool) :
    Hypernet d (List.replicate 3 (environmentInterface k h)[i]) [(environmentInterface k h)[i]] :=
  (CopyingNested.Row.graph (CopyingDouble.Frame.sort k h i) associateRight d).reboundary
    (congrArg (List.replicate 3) (CopyingDouble.Frame.sort_wire k h i))
    (congrArg List.singleton (CopyingDouble.Frame.sort_wire k h i))

noncomputable def family (associateRight : Bool) (e : (graph arity N k h inputs d).Edge) :
    Hypernet d ((alphabet d).signature.input ((graph arity N k h inputs d).edgeLabel e))
      ((alphabet d).signature.output ((graph arity N k h inputs d).edgeLabel e)) := by
  cases d <;> rcases e with b | i
  all_goals first | exact branches b | exact row i associateRight

/-- One finite original common frame fixes all branch and resource orders. -/
noncomputable def normal (associateRight : Bool) :
    Hypernet d (List.replicate N .term) (environmentInterface k h) :=
  (graph arity N k h inputs d).expand (family inputs branches associateRight)

/-- Associating the original resource merges changes only genuine sharing
trees; arbitrary branches, including divergent or boxed ones, remain reflexive. -/
noncomputable def witness (free : ∀ b, FocusFree (branches b)) :
    FillingWitness SharingTreeAlgebra.template (normal inputs branches false) (normal inputs branches true) := by
  apply FillingWitness.expand
  intro e
  cases d <;> rcases e with b | i
  all_goals first
    | exact FillingWitness.refl (branches b) (free b)
    | exact (CopyingNested.Row.witness (CopyingDouble.Frame.sort k h i) _).reboundary
        (congrArg (List.replicate 3) (CopyingDouble.Frame.sort_wire k h i))
        (congrArg List.singleton (CopyingDouble.Frame.sort_wire k h i))
end Hypernets.Copying.CopyingMerge.Frame

namespace Hypernets.Copying.CopyingMerge
open Graph
variable {d a b c k h : Nat}
    (A : Hypernet d (List.replicate a .term) (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))
    (C : Hypernet d (List.replicate c .term) (environmentInterface k h))

def branches : (tag : Fin 3) → Hypernet d (List.replicate (Inputs.arity a b c tag) .term)
    (environmentInterface k h)
  | ⟨0,_⟩ => A
  | ⟨1,_⟩ => B
  | ⟨2,_⟩ => C
  | ⟨n+3,bound⟩ => False.elim (by omega)

/-- The common normal graph has the exact original A-then-B-then-C input order. -/
noncomputable def normal (associateRight : Bool) :
    Hypernet d (List.replicate (a+b+c) .term) (environmentInterface k h) :=
  Frame.normal (Inputs.bijection a b c) (branches A B C) associateRight

noncomputable def normalWitness (af : FocusFree A) (bf : FocusFree B) (cf : FocusFree C) :
    FillingWitness SharingTreeAlgebra.template (normal A B C false) (normal A B C true) := by
  apply Frame.witness
  intro tag
  rcases CopyingDouble.Frame.triple tag with rfl | rfl | rfl
  · exact af
  · exact bf
  · exact cf
end Hypernets.Copying.CopyingMerge

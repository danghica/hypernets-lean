import Hypernets.Copying.LambdaPermutationPair

/-! The original abstraction shell preserves every typed boundary isomorphism,
including the mandatory single-use sharing graphs after its operand. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AbstractionShell
open Graph Translation
variable {d k h} {G H : Hypernet d [.thunk 1] (environmentInterface k h)}

/-- The literal abstraction clause with its box supplied separately. -/
def graph {d k h} (B : Hypernet d [.thunk 1] (environmentInterface k h)) :
    Hypernet d [.term] (environmentInterface k h) :=
  Serial.net (Serial.net (primitiveNet d (.operation .lam)) B) (singleUse d k h)

/-- The singleton operand input forces matching with the original lambda operation. -/
theorem prefix_compatible (f : BoundaryIso G H) :
    BoundarySerial.Compatible (BoundaryIso.refl (primitiveNet d (.operation .lam))) f := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  have hj := (f.inputs.toFun i).isLt
  change (i : Nat) < 1 at hi
  change (f.inputs.toFun i).val < 1 at hj
  change ((BoundaryIso.refl _).outputs.toFun i).val = _
  have eq : (BoundaryIso.refl (primitiveNet d (.operation .lam))).outputs.toFun i = i := by
    apply Port.output.inj (Internal := (primitiveNet d (.operation .lam)).Internal) (inputs := 1)
    exact (BoundaryIso.map_output (BoundaryIso.refl (primitiveNet d (.operation .lam))) i).symm
  rw [eq]
  omega

def prefixIso (f : BoundaryIso G H) :
    BoundaryIso (Serial.net (primitiveNet d (.operation .lam)) G)
      (Serial.net (primitiveNet d (.operation .lam)) H) :=
  BoundarySerial.iso (BoundaryIso.refl _) f (prefix_compatible f)

/-- The original single-use forests realise exactly the operand's output action. -/
def forestIso (f : BoundaryIso G H) :
    BoundaryIso (singleUse d k h) (singleUse d k h) :=
  SingleUseBoundary.ofTyped f.outputs (fun i => f.output_label i) d

theorem forest_compatible (f : BoundaryIso G H) :
    BoundarySerial.Compatible (prefixIso f) (forestIso f) := by
  intro i
  have left := BoundarySerial.iso_output (BoundaryIso.refl _) f (prefix_compatible f) i
  rw [BoundaryIso.map_output] at left
  have right := SingleUseBoundary.ofTyped_input f.outputs (fun i => f.output_label i) d i
  rw [BoundaryIso.map_input] at right
  exact (Port.output.inj left).trans (Port.input.inj right).symm

/-- Unconditional constructor congruence for the literal Figure 16 abstraction clause. -/
def iso (f : BoundaryIso G H) : BoundaryIso (graph G) (graph H) :=
  BoundarySerial.iso (prefixIso f) (forestIso f) (forest_compatible f)

/-- Abstraction-shell extension retains the operand's resource permutation exactly. -/
theorem iso_output (f : BoundaryIso G H) (i : Fin (environmentInterface k h).length) :
    (iso f).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have left := BoundarySerial.iso_output (prefixIso f) (forestIso f) (forest_compatible f) i
  have right := SingleUseBoundary.ofTyped_output f.outputs (fun i => f.output_label i) d i
  rw [BoundaryIso.map_output] at right
  exact left.trans (congrArg Port.output (Port.output.inj right))
end Hypernets.Copying.AbstractionShell

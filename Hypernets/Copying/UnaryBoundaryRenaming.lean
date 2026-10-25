import Hypernets.Copying.SingleUseBoundaryRenaming

/-! The original unary translation preserves every typed boundary isomorphism,
including the mandatory single-use sharing graphs after its operand. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph
variable {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}

/-- The singleton operand input forces matching with the original unary operation. -/
theorem unary_prefix_compatible (o : Unary) (f : BoundaryIso G H) :
    BoundarySerial.Compatible (BoundaryIso.refl (primitiveNet d (.operation (.unary o)))) f := by
  intro i
  apply Fin.ext
  have hi := i.isLt
  have hj := (f.inputs.toFun i).isLt
  change (i : Nat) < 1 at hi
  change (f.inputs.toFun i).val < 1 at hj
  change ((BoundaryIso.refl _).outputs.toFun i).val = _
  have eq : (BoundaryIso.refl (primitiveNet d (.operation (.unary o)))).outputs.toFun i = i := by
    apply Port.output.inj (Internal := (primitiveNet d (.operation (.unary o))).Internal) (inputs := 1)
    exact (BoundaryIso.map_output (BoundaryIso.refl (primitiveNet d (.operation (.unary o)))) i).symm
  rw [eq]
  omega

def unaryPrefixIso (o : Unary) (f : BoundaryIso G H) :
    BoundaryIso (Serial.net (primitiveNet d (.operation (.unary o))) G)
      (Serial.net (primitiveNet d (.operation (.unary o))) H) :=
  BoundarySerial.iso (BoundaryIso.refl _) f (unary_prefix_compatible o f)

/-- The original single-use forests realise exactly the operand's output action. -/
def unaryForestIso (f : BoundaryIso G H) :
    BoundaryIso (singleUse d k h) (singleUse d k h) :=
  SingleUseBoundary.ofTyped f.outputs (fun i => f.output_label i) d

theorem unary_forest_compatible (o : Unary) (f : BoundaryIso G H) :
    BoundarySerial.Compatible (unaryPrefixIso o f) (unaryForestIso f) := by
  intro i
  have left := BoundarySerial.iso_output (BoundaryIso.refl _) f (unary_prefix_compatible o f) i
  rw [BoundaryIso.map_output] at left
  have right := SingleUseBoundary.ofTyped_input f.outputs (fun i => f.output_label i) d i
  rw [BoundaryIso.map_input] at right
  exact (Port.output.inj left).trans (Port.input.inj right).symm

/-- Unconditional constructor congruence for the literal Figure 16 unary clause. -/
def unary_boundaryIso (o : Unary) (f : BoundaryIso G H) : BoundaryIso (unary o G) (unary o H) :=
  BoundarySerial.iso (unaryPrefixIso o f) (unaryForestIso f) (unary_forest_compatible o f)

/-- Repeated unary extension retains the operand's resource permutation exactly. -/
theorem unary_boundaryIso_output (o : Unary) (f : BoundaryIso G H) (i : Fin (environmentInterface k h).length) :
    (unary_boundaryIso o f).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have left := BoundarySerial.iso_output (unaryPrefixIso o f) (unaryForestIso f) (unary_forest_compatible o f) i
  have right := SingleUseBoundary.ofTyped_output f.outputs (fun i => f.output_label i) d i
  rw [BoundaryIso.map_output] at right
  exact left.trans (congrArg Port.output (Port.output.inj right))
end Hypernets.Copying.Translation

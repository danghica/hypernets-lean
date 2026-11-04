import Hypernets.Copying.WeakeningTranslationSteps

/-! Nonempty mixed environments and nested-box regression instances of the
new weakening laws. These use the unchanged translation, not a new syntax. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Examples
open Graph BoxPullWeakening

/-- A translated lambda whose body uses an outer variable and an ambient atom.
Both environments have two resources, and the graph already contains a box. -/
def nestedBody : Hypernet 1 [.term] (environmentInterface 2 2) :=
  Translation.term (.lam (.app (.var 2) (.atom 1)) : Term 2 2)

theorem nestedBody_free : FocusFree nestedBody :=
  Translation.term_focusFree _

/-- Another box encloses the translated body while retaining one free variable
and both atoms. The new resource can have either sort. -/
noncomputable def mixed_box (s : ShareSort) :
    Calculation
      (Serial.net (BoxPullWeakening.left (n := 1) (k := 1) nestedBody s)
        (Translation.singleUse 2 (variables s 1) (atoms s 2)))
      (extend (Serial.net (box (bound := 1) (freeVariables := 1) nestedBody)
        (Translation.singleUse 2 1 2)) s) :=
  boxed_resources (n := 1) (k := 1) nestedBody s nestedBody_free

/-- The actual abstraction clause retains both the existing inner box and its
new outer box, together with the unchanged old distributor. -/
noncomputable def mixed_abstraction (s : ShareSort) :
    Calculation (Translation.abstraction (betaBody (k := 1) nestedBody s))
      (extend (Translation.abstraction (k := 1) nestedBody) s) :=
  abstraction_extend nestedBody s nestedBody_free

/-- Allocation followed by dereference composes the two genuine unary steps;
no totality or successful execution of the supplied graph is assumed. -/
noncomputable def allocation_read (s : ShareSort) :
    Calculation (Translation.unary .deref (Translation.unary .ref (extend nestedBody s)))
      (extend (Translation.unary .deref (Translation.unary .ref nestedBody)) s) :=
  unary_step .deref s (unary_extend .ref nestedBody s nestedBody_free)

/-- The second old atom moves right when a term is inserted before the atom
block; the new term occupies precisely the old block boundary. -/
theorem term_boundary_order :
    ((SingleUseExtension.boundary 2 2 .term).inputs.toFun ⟨false,⟨3,by decide⟩⟩).val = 4 ∧
    ((SingleUseExtension.boundary 2 2 .term).inputs.toFun ⟨true,⟨0,by decide⟩⟩).val = 2 := by decide

/-- A new atom is inserted before the old atom block, not appended after it.
The old variables stay fixed and the old atoms shift together. -/
theorem atom_boundary_order :
    ((SingleUseExtension.boundary 2 2 .atom).inputs.toFun ⟨false,⟨1,by decide⟩⟩).val = 1 ∧
    ((SingleUseExtension.boundary 2 2 .atom).inputs.toFun ⟨true,⟨0,by decide⟩⟩).val = 2 ∧
    ((SingleUseExtension.boundary 2 2 .atom).inputs.toFun ⟨false,⟨3,by decide⟩⟩).val = 4 := by decide

end Hypernets.Copying.Weakening.Examples

import Hypernets.Copying.OneWayComposition

/-! The paper's micro-beta and reference-creation pre-templates, formed from
exactly the existing operational rules with their stable-argument premises.
Output closure is proved here; robustness is a separate obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Application
/-- The box blocks operation-only paths through the closure, and the stable
argument has no term output. This proves output closure before beta reduction. -/
theorem before_oneWay {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) : OneWay (before B G) := by
  apply OneWay.serial_right
  apply OneWay.tensor
  · apply OneWay.serial_right
    exact OneWay.box _
  · exact oneWay_of_stable_outputs G stable.outputs
end Application

namespace OperationalTemplates
/-- The two operational template families used in Figure 22. -/
inductive Kind where
  | microBeta
  | referenceCreation

/-- Original token-erased graph rules, with stability and focus freedom retained. -/
inductive Literal : Kind → {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | beta {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
      (G : Hypernet (d+1) [.term] O) (free : FocusFree B) (stable : Stable G) :
      Literal .microBeta (Application.before B G) (Application.after B G)
  | reference {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
      Literal .referenceCreation (Allocation.before G) (Allocation.after G)

/-- Graph carrier names are immaterial, independently on each side. -/
inductive Pair (kind : Kind) : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (literal : Literal kind A B) (right : DeepIso B H) : Pair kind G H

theorem Literal.focusFree {kind d I O} {G H : Hypernet d I O} (pair : Literal kind G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | beta B G free stable =>
    exact ⟨Application.before_labels _ B G free stable.focusFree
      (by intro m eq; cases eq) (by intro m eq; cases eq),
      Application.after_labels _ B G free stable.focusFree⟩
  | reference G stable =>
    exact ⟨Serial.focusFree_net
      (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq)) stable.focusFree,
      Allocation.after_focusFree G stable.focusFree⟩

/-- Beta's left side is one-way even when its body is arbitrary. Reference
creation has no term outputs on either side, by the original stability premise. -/
theorem Literal.outputClosed {kind d I O} {G H : Hypernet d I O} (pair : Literal kind G H) :
    OneWay G := by
  cases pair with
  | beta B G free stable => exact Application.before_oneWay B G stable
  | reference G stable => exact oneWay_of_stable_outputs _ stable.outputs

theorem Pair.focusFree {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f p g => exact ⟨(allLabels_iso_iff _ f).mpr p.focusFree.1,
      (allLabels_iso_iff _ g).mp p.focusFree.2⟩

theorem Pair.outputClosed {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    OneWay G := by
  cases pair with
  | witness f p g => exact (OneWay.iso_iff f).mpr p.outputClosed

/-- The concrete pre-template for either original operational family. -/
def template (kind : Kind) : PreTemplate where
  Rel := Pair kind
  focus_free pair := pair.focusFree

/-- Both operational templates satisfy output closure, without assuming a
simulation, robustness, or the desired program equivalence. -/
theorem template_outputClosed (kind : Kind) : (template kind).OutputClosed :=
  fun pair => .inl pair.outputClosed

/-- A literal rule's interface has precisely the single term input. -/
theorem Literal.input {kind d I O} {G H : Hypernet d I O} (pair : Literal kind G H) : I = [.term] := by
  cases pair <;> rfl

/-- Token erasure really refers to an existing local compute step. -/
theorem Literal.compute {kind d I O} {G H : Hypernet d I O} (pair : Literal kind G H) :
    ∃ v w, Combined.Local G v H w := by
  cases pair with
  | beta B G free stable => exact ⟨_,_,.beta B G stable⟩
  | reference G stable => exact ⟨_,_,.allocate G stable⟩

/-- Arbitrary carrier choices preserve the actual compute step, not only the
unlabelled graph relation. -/
theorem Pair.compute {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    ∃ v w, Combined.Rewrite G v H w := by
  cases pair with
  | witness f p g =>
    obtain ⟨v,w,step⟩ := p.compute
    exact ⟨_,_,.rename f.symm g (.local step)⟩
/-- Both sides use the same external input coordinate; the actual compute
transition returns to search there after renaming either graph independently. -/
theorem Pair.entry {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    ∃ i : Fin I.length, Combined.Step ⟨G,(.rewrite,.input i)⟩ ⟨H,(.search,.input i)⟩ := by
  cases pair with
  | witness f p g =>
    cases p with
    | beta B G free stable => exact ⟨0,.rewrite (.rename f.symm g (.local (.beta _ _ stable)))⟩
    | reference G stable => exact ⟨0,.rewrite (.rename f.symm g (.local (.allocate _ stable)))⟩

end OperationalTemplates
end Hypernets.Copying

import Hypernets.Copying.LoweringPredicates
import Hypernets.Copying.CombinedPadding

/-! Every primitive local match in the representable fragment descends to the
smaller allowance. Both the successor depth invariant and the actual rewrite
are proved; no determinism or matching-independence hypothesis is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace Lowering

/-- The recovery isomorphism in the original recursive padding presentation. -/
def recover_raise {d I O} (G : Hypernet (d+1) I O) (fit : Fits G) :
    DeepIso (raise d (graph G)) G := by
  rw [← Padding.graph_eq_raise]; exact recover G fit

/-- Reflect a specified padded representation using the structural left inverse. -/
noncomputable def fromRaised {d I O} {G : Hypernet d I O} {H : Hypernet (d+1) I O}
    (f : DeepIso (raise d G) H) : DeepIso G (graph H) :=
  (roundtrip G).symm.trans (graphIso (Combined.graphIsoOfRaise f))

end Lowering
namespace Combined

/-- A known smaller input-rooted rule transports to lowered presentations.
The padded target certificate also proves preservation of representability. -/
theorem lower_input_rule {d I O} {L R : Hypernet d I O} {G H : Hypernet (d+1) I O}
    (i : Fin I.length) (f : DeepIso (raise d L) G) (g : DeepIso (raise d R) H)
    (step : Rewrite L (.input i) R (.input i)) :
    Lowering.Fits H ∧ Rewrite (Lowering.graph G) (.input i) (Lowering.graph H) (.input i) :=
  ⟨(Lowering.fits_iso_iff g).mp (Lowering.fits_raise R),
    rewrite_input_iso i (Lowering.fromRaised f) (Lowering.fromRaised g) step⟩

/-- All local families descend, with stability and copyability discharged from
their actual predicates and beta's box body recovered from the source graph. -/
theorem local_lowering {d I O} {G H : Hypernet (d+1) I O} {v w}
    (step : Local G v H w) (fit : Lowering.Fits G) :
    Lowering.Fits H ∧ Rewrite (Lowering.graph G) v (Lowering.graph H) w := by
  cases step with
  | allocate G stable =>
    have recovered := Lowering.recover_raise G stable.fits
    exact lower_input_rule (I := [.term]) 0
      ((Allocation.before_raise _).trans (Allocation.before_congr recovered))
      ((Allocation.after_raise _).trans (Allocation.after_congr recovered))
      (.local (.allocate _ stable.lower))
  | read T =>
    apply lower_input_rule (d := d) ⟨0,by simp [Dereference.inputs]⟩
      (L := Dereference.before T d) (R := Dereference.after T d)
    · rw [Dereference.before_raise]; exact DeepIso.refl _
    · rw [Dereference.after_raise]; exact DeepIso.refl _
    · exact .local (.read T d)
  | assign T G stable =>
    have recovered := Lowering.recover_raise G stable.fits
    exact lower_input_rule ⟨0,by simp [Assignment.inputs]⟩
      ((Assignment.before_raise T _).trans (Assignment.before_congr (Net.Iso.refl _) recovered))
      ((Assignment.after_raise T _).trans (Assignment.after_congr (Net.Iso.refl _) recovered))
      (.local (.assign T _ stable.lower))
  | same T =>
    apply lower_input_rule (d := d) ⟨0,by simp [AtomEquality.Same.inputs]⟩
      (L := AtomEquality.Same.before T d) (R := AtomEquality.Same.after T d)
    · rw [AtomEquality.Same.before_raise]; exact DeepIso.refl _
    · rw [AtomEquality.Same.after_raise]; exact DeepIso.refl _
    · exact .local (.same T d)
  | different T U =>
    apply lower_input_rule (d := d) ⟨0,by simp [AtomEquality.Different.inputs]⟩
      (L := AtomEquality.Different.before T U d) (R := AtomEquality.Different.after T U d)
    · rw [AtomEquality.Different.before_raise]; exact DeepIso.refl _
    · rw [AtomEquality.Different.after_raise]; exact DeepIso.refl _
    · exact .local (.different T U d)
  | beta B G stable =>
    have closureFit := ((Lowering.fits_tensor _ _).mp ((Lowering.fits_serial _ _).mp fit).2).1
    cases d with
    | zero => exact False.elim (Copyable.lambda_not_fits B closureFit)
    | succ d =>
      have bodyFit := (Copyable.lambda_fits_iff B).mp closureFit
      have recB := Lowering.recover_raise B bodyFit
      have recG := Lowering.recover_raise G stable.fits
      exact lower_input_rule (I := [.term]) 0
        ((Application.before_raise _ _).trans (Application.before_congr recB recG))
        ((Application.after_raise _ _).trans (Application.after_congr recB recG))
        (.local (.beta _ _ stable.lower))
  | copy T G copyable =>
    have payloadFit := ((Lowering.fits_serial _ _).mp fit).2
    have recovered := Lowering.recover_raise G payloadFit
    exact lower_input_rule ⟨0,by simp⟩
      ((CopyRule.before_raise T _).trans (CopyRule.before_congr (Net.Iso.refl _) recovered))
      ((CopyRule.after_raise T _).trans (CopyRule.after_congr (Net.Iso.refl _) recovered))
      (.local (.copy T _ (copyable.lower payloadFit)))
  | unaryArithmetic _ n =>
    exact lower_input_rule (I := [.term]) 0
      (Arithmetic.unaryBefore_raise d n) (Arithmetic.number_raise_iso d (Arithmetic.neg n))
      (.local (.unaryArithmetic d n))
  | binaryArithmetic o _ m n =>
    exact lower_input_rule (I := [.term]) 0
      (Arithmetic.binaryBefore_raise o d m n) (Arithmetic.number_raise_iso d (o.eval m n))
      (.local (.binaryArithmetic o d m n))

end Combined
end Hypernets.Copying

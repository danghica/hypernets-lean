import Hypernets.Copying.BoxPullWeakeningBetaDiamond
import Hypernets.Copying.CopyFillingWitness

/-! Original copying steps for the literal BPullW lambda payload, and the
genuine duplicated BPullW certificate. The final Idem correction of the
new distributor row is a separate geometric obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

/-- Pulling a weakening through any serial prefix retains the paper's
counted variable/atom interfaces on both sides. -/
def serial_extend {d I J k h} (P : Hypernet d I J)
    (G : Hypernet d J (environmentInterface k h)) (s : ShareSort) :
    DeepIso (Serial.net P (extend G s)) (extend (Serial.net P G) s) := by
  rw [extend_eq,extend_eq]
  exact (serial_output P (adjoin G s) (adjoin_interface s k h)).trans
    (CopyRule.reboundaryIso (SerialPull.iso P G s) rfl (adjoin_interface s k h))

/-- The actual lambda payload pair supplied by BPullW, with one original
literal occurrence and the unchanged lambda head retained in its context. -/
noncomputable def payloadWitness {d k h}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) (name : Nat) (free : FocusFree B) :
    FillingWitness template (lambdaPayload (betaBody B s)) (extend (lambdaPayload B) s) :=
  ((FillingWitness.refl (primitiveNet (d+1) (.operation .lam))
    (by intro e m eq; cases eq)).serial
      (FillingWitness.of_rel name (lambda_literal B s free))).congr
    (DeepIso.refl _) (serial_extend _ (Translation.lambdaBox B) s)

theorem extend_rewrite {d I k h} {G H : Hypernet d I (environmentInterface k h)}
    (s : ShareSort) (i j : Fin I.length)
    (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (extend G s) (.input i) (extend H s) (.input j) := by
  rw [extend_eq,extend_eq]
  exact rewrite_reboundary rfl (adjoin_interface s k h)
    (adjoin_rewrite (A := List.replicate k .term) (B := List.replicate h .atom) s i j step)

/-- The common contraction tree is retained; the outside weakening remains
separate from the actual copyable payload. -/
noncomputable def copy_sourceWitness {d n k h}
    (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) (free : FocusFree B) :
    FillingWitness template (CopyRule.before T (lambdaPayload (betaBody B s)))
      (extend (CopyRule.before T (lambdaPayload B)) s) :=
  ((payloadWitness B s 0 free).copyingBefore T).congr (DeepIso.refl _)
    (serial_extend (CopyRule.tree T (d+1)) (lambdaPayload B) s)

/-- Copying duplicates the complete original BPullW occurrence. The target
here is the explicit intermediate graph before contracting its duplicated
weakenings by Idem; it is not asserted to be an actual copyable payload. -/
noncomputable def copy_intermediateWitness {d n k h}
    (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (s : ShareSort) (free : FocusFree B) :
    FillingWitness template (CopyRule.after T (lambdaPayload (betaBody B s)))
      (CopyRule.after T (extend (lambdaPayload B) s)) :=
  (payloadWitness B s 0 free).copyingAfter (payloadWitness B s 1 free) T

/-- Both actual original copying transitions, including all residual sharing
tree inputs and both ordered output distributor forests. The outside step
copies only the original lambda payload, preserving the separate weakening. -/
theorem copy_steps {d n k h} (T : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (s : ShareSort) :
    Rewrite (CopyRule.before T (lambdaPayload (betaBody B s))) (.input ⟨0,by simp⟩)
      (CopyRule.after T (lambdaPayload (betaBody B s))) (.input ⟨0,by simp⟩) ∧
    Rewrite (extend (CopyRule.before T (lambdaPayload B)) s) (.input ⟨0,by simp⟩)
      (extend (CopyRule.after T (lambdaPayload B)) s) (.input ⟨0,by simp⟩) :=
  ⟨.local (.copy T _ (.lambda _)),
    extend_rewrite s ⟨0,by simp⟩ ⟨0,by simp⟩ (.local (.copy T _ (.lambda B)))⟩

end Hypernets.Copying.BoxPullWeakening

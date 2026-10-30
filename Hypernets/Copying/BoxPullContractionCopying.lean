import Hypernets.Copying.BoxPullContractionBetaDiamond
import Hypernets.Copying.CopyFillingWitness

/-! Original copying steps and the duplicated literal BPullC certificate.
The intermediate has two external contractions followed by the actual output
distributor; sharing interchange is a separate residual obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined

/-- Pulling the literal contraction through an unchanged serial prefix
preserves the original counted term and atom interfaces. -/
def serial_contract {d I J k h} (s : ShareSort) (P : Hypernet d I J)
    (G : Hypernet d J (environmentInterface (variables s k 2) (atoms s h 2))) :
    DeepIso (Serial.net P (contract s G)) (contract s (Serial.net P G)) := by
  rw [contract_eq,contract_eq]
  exact (BoxPullWeakening.serial_output P _ (one_interface s k h)).trans
    ((CopyRule.reboundaryIso (SerialPull.iso s P _) rfl (one_interface s k h)).trans
      (CopyRule.reboundaryIso (merge_congr s
        (BoxPullWeakening.serial_output P G (two_interface s k h))) rfl (one_interface s k h)))

/-- The lambda head remains in the common context; the hole is precisely
the literal box-contraction pair, with its original arbitrary body. -/
noncomputable def payloadWitness {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (name : Nat) (free : FocusFree G) :
    FillingWitness template (lambdaPayload (betaBody s G)) (contract s (lambdaPayload G)) :=
  ((FillingWitness.refl (primitiveNet (d+1) (.operation .lam))
    (by intro e m eq; cases eq)).serial
      (FillingWitness.of_rel name (lambda_literal s G free))).congr
    (DeepIso.refl _) (serial_contract s _ (Translation.lambdaBox G))

/-- An actual rewrite may be surrounded by the literal output contraction;
only ordered interface casts and the original expansion rule are used. -/
theorem contract_rewrite {d I k h} (s : ShareSort)
    {G H : Hypernet d I (environmentInterface (variables s k 2) (atoms s h 2))}
    (i j : Fin I.length) (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (contract s G) (.input i) (contract s H) (.input j) := by
  rw [contract_eq,contract_eq]
  exact rewrite_reboundary rfl (one_interface s k h)
    (merge_rewrite (I := I) (A := List.replicate k .term) (B := List.replicate h .atom) s i j
      (rewrite_reboundary rfl (two_interface s k h) step))

/-- The actual contraction tree and lambda head are retained around one
original literal template occurrence. -/
noncomputable def copy_sourceWitness {d n k h} (s : ShareSort)
    (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (free : FocusFree G) :
    FillingWitness template (CopyRule.before T (lambdaPayload (betaBody s G)))
      (contract s (CopyRule.before T (lambdaPayload G))) :=
  ((payloadWitness s G 0 free).copyingBefore T).congr (DeepIso.refl _)
    (serial_contract s (CopyRule.tree T (d+1)) (lambdaPayload G))

/-- Duplication creates two genuine occurrences of the original pair. The
right graph is the explicit intermediate before output sharing interchange;
it is not asserted to be a copyable payload. -/
noncomputable def copy_intermediateWitness {d n k h} (s : ShareSort)
    (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (free : FocusFree G) :
    FillingWitness template (CopyRule.after T (lambdaPayload (betaBody s G)))
      (CopyRule.after T (contract s (lambdaPayload G))) :=
  (payloadWitness s G 0 free).copyingAfter (payloadWitness s G 1 free) T

/-- Both branches perform the original copying transition with the actual
copyable lambda payload. The external contraction remains outside that
payload, and all residual tree inputs and distributor rows are retained. -/
theorem copy_steps {d n k h} (s : ShareSort) (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :
    Rewrite (CopyRule.before T (lambdaPayload (betaBody s G))) (.input ⟨0,by simp⟩)
      (CopyRule.after T (lambdaPayload (betaBody s G))) (.input ⟨0,by simp⟩) ∧
    Rewrite (contract s (CopyRule.before T (lambdaPayload G))) (.input ⟨0,by simp⟩)
      (contract s (CopyRule.after T (lambdaPayload G))) (.input ⟨0,by simp⟩) :=
  ⟨.local (.copy T _ (.lambda _)),
    contract_rewrite s ⟨0,by simp⟩ ⟨0,by simp⟩ (.local (.copy T _ (.lambda G)))⟩

end Hypernets.Copying.BoxPullContraction

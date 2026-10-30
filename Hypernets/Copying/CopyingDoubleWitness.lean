import Hypernets.Copying.CopyingDouble
import Hypernets.Copying.CopyingInputWitness

/-! Actual residual copying certificates after entering another original tree
input. Unrelated branches and the canonical resource distributors remain in
the shared context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble
open Graph

/-- Assemble any actual paired retained branch beneath the original active
payload and the two-use term/atom distributors. -/
def afterWithWitness {T : PreTemplate} {d n k h}
    (H : Hypernet d [.term] (environmentInterface k h)) (free : FocusFree H)
    {A B : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (w : FillingWitness T A B) : FillingWitness T (afterWith H A) (afterWith H B) := by
  apply FillingWitness.serial
  · apply FillingWitness.reboundary
    apply FillingWitness.parallel (CopyRule.pairBoundary (n+1) k h)
    intro b; cases b
    · exact FillingWitness.refl H free
    · exact w
  · exact FillingWitness.refl (Translation.environmentDistributor d k h 2)
      (Translation.allLabels_tensor _
        (Distributor.allLabels_atDepth _ .term k 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
        (Distributor.allLabels_atDepth _ .atom h 2 d (by intro m eq; cases eq) (by intro m eq; cases eq)))

/-- After copying input zero, copying input one leaves one genuine copying
pair in the retained branch; the active first payload is part of the context. -/
noncomputable def secondWitness {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template (CopyRule.after T H) (afterSecond T H) :=
  afterWithWitness H free (FillingWitness.of_rel 0
    (CopyingTemplate.literal (CopyRule.residualTree T) H copyable free))

/-- The opposite order has the same literal residual copying certificate,
transported through the actual input-swap context. -/
noncomputable def oppositeWitness {d n k h} (T : ContractionTree .term (n+2))
    (H : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template
      (CopyingInputPermutation.net
        (CopyRule.after (CopyingInputPermutation.reordered T (exchangeInputs n)) H)
        (exchangeInputs n))
      (opposite T H) :=
  (secondWitness (CopyingInputPermutation.reordered T (exchangeInputs n)) H copyable free).inputPermutation
    (exchangeInputs n)

end Hypernets.Copying.CopyingDouble

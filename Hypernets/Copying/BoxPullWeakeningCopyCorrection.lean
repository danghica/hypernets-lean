import Hypernets.Copying.BoxPullWeakeningCopyPartition
import Hypernets.Copying.BoxPullWeakeningPointed
import Hypernets.Copying.ContractionIdempotenceEquivalence

/-! The exact Idem correction required by the BPullW copying overlap. Both
steps are original filling witnesses and their endpoint is the literal
outside-weakening reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.CopyRow
open Graph Combined
variable {d n k h} (T : ContractionTree .term (n+1))
  (H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

/-- The second Idem witness ends at the actual outside-weakening reduct,
using the proved exhaustive reconstruction rather than an assumed equation. -/
noncomputable def finalSecond (free : FocusFree H) :
    FillingWitness ContractionIdempotence.template (intermediate T H s)
      (extend (CopyRule.after T H) s) :=
  (second T H s free).congr (DeepIso.refl _) (RetainedCopy.normalizationIso T H s).symm

theorem intermediate_closed (closed : HoleFree H) : HoleFree (intermediate T H s) := by
  have original := CopyRule.holeFree_after T (extend H s)
    ((extend_allLabels _ H s).mpr ⟨closed,by intro h eq; cases eq⟩)
  cases d
  all_goals
    intro e
    cases e with
    | inl e =>
      rcases e with ⟨e,ne⟩
      cases e with
      | none => exact False.elim (ne rfl)
      | some e => exact original e.val
    | inr e => exact (ContractionIdempotence.Step.idem _ s).holeFree.1 e

theorem outside_closed (closed : HoleFree H) : HoleFree (extend (CopyRule.after T H) s) :=
  (extend_allLabels _ _ s).mpr ⟨CopyRule.holeFree_after T H closed,by intro h eq; cases eq⟩

/-- Preserve the host's global hole freedom while replacing its selected
component by another proved hole-free graph. -/
theorem plug_closed {d I O} (C : Hypernet d I O) (e : C.Edge)
    {A B : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (closed : HoleFree (C.plug e A)) (replacement : HoleFree B) : HoleFree (C.plug e B) := by
  intro x
  cases x with
  | inl x => exact closed (.inl x)
  | inr x => exact replacement x

/-- In every focus-free closing host, the two Idem corrections preserve exact
execution costs at the actual unchanged host token. Only one actual endpoint
root is supplied; the intermediate root is proved by original search. -/
theorem exact_at (freeH : FocusFree H) (closedH : HoleFree H)
    (C : Hypernet d [.term] []) (freeC : FocusFree C) (e : C.Edge)
    (hi : List.replicate (n+1) .term = (alphabet d).signature.input (C.edgeLabel e))
    (ho : environmentInterface (variables s k) (atoms s h) =
      (alphabet d).signature.output (C.edgeLabel e))
    (closed : HoleFree (C.plug e ((CopyRule.after T (extend H s)).reboundary hi ho)))
    (mode) (v : C.Vertex) (typed : C.vertexLabel v = .term) (nonrewrite : mode ≠ .rewrite)
    (rooted : StateClass.Rooted (StateClass.ofState
      ⟨d,C.plug e ((CopyRule.after T (extend H s)).reboundary hi ho),
        (mode,Net.Replacement.host C e ((CopyRule.after T (extend H s)).reboundary hi ho) v)⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,C.plug e ((CopyRule.after T (extend H s)).reboundary hi ho),
        (mode,Net.Replacement.host C e ((CopyRule.after T (extend H s)).reboundary hi ho) v)⟩)
      (StateClass.ofState ⟨d,C.plug e ((extend (CopyRule.after T H) s).reboundary hi ho),
        (mode,Net.Replacement.host C e ((extend (CopyRule.after T H) s).reboundary hi ho) v)⟩) := by
  have mid : HoleFree (C.plug e ((intermediate T H s).reboundary hi ho)) :=
    plug_closed C e closed (intermediate_closed T H s closedH)
  have last : HoleFree (C.plug e ((extend (CopyRule.after T H) s).reboundary hi ho)) :=
    plug_closed C e closed (outside_closed T H s closedH)
  have one := NullaryExecution.plug_pointed_class_exact_equiv
    ContractionIdempotence.template_noInputs ContractionIdempotence.template_paddingClosed
    C freeC e ((first T H s freeH).reboundary hi ho) closed mid mode v typed nonrewrite rooted
  have two := NullaryExecution.plug_pointed_class_exact_equiv
    ContractionIdempotence.template_noInputs ContractionIdempotence.template_paddingClosed
    C freeC e ((finalSecond T H s freeH).reboundary hi ho) mid last mode v typed nonrewrite one.2
  exact ⟨one.1.1.trans two.1.1,two.1.2.trans one.1.2⟩

end Hypernets.Copying.BoxPullWeakening.CopyRow

import Hypernets.Copying.ContextualRobustness
import Hypernets.Copying.BoxPermutationSafety

/-! The paper's no-term-input safety criterion for actual recursive specimens. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- Every input of every related fragment has a non-term wire type. -/
def PreTemplate.NoTermInputs (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → ∀ i : Fin I.length, I[i] ≠ .term

/-- A fragment with no term input is one way, irrespective of its internal body. -/
theorem oneWay_of_no_term_inputs {d I O} (G : Hypernet d I O)
    (none : ∀ i : Fin I.length, I[i] ≠ .term) : OneWay G := by
  rw [oneWay_iff_paths]
  intro i j term
  exact False.elim (none i term)

/-- Output closure is automatic on both sides of this class of pre-templates. -/
theorem PreTemplate.NoTermInputs.outputClosed {T : PreTemplate} (none : T.NoTermInputs) : T.OutputClosed :=
  fun rel => .inl (oneWay_of_no_term_inputs _ (none rel))

/-- An actual original shallow hole cannot be retained in a hole-free filled
state. Its certificate must be a genuine template replacement. -/
theorem DeepFillingEdge.relation_at_hole {T d I O} {C : Hypernet d I O} {F K e}
    (edge : DeepFillingEdge T C F K e) {h : Hole}
    (label : C.edgeLabel e = primitiveLabel d (.hole h))
    (closed : HoleFree (C.expand F)) : T.Rel (F e) (K e) := by
  cases edge with
  | retained l r =>
    have hf := closed ⟨e,l.edge⟩
    change LabelAll (fun p => ∀ h, p ≠ .hole h) d ((F e).edgeLabel l.edge) at hf
    rw [l.edge_label,label] at hf
    cases d <;> exact False.elim (hf h rfl)
  | filled h label rel => exact rel
  | boxed b box inner l r => rw [box] at label; cases label

namespace Specimen
/-- A typed term token cannot enter any replaced hole of a no-term-input
pre-template, even when other replacements occur deep inside boxes. -/
theorem not_entering {T Allowed} (S : Specimen T Allowed) (none : T.NoTermInputs) : ¬ S.Entering := by
  rintro ⟨e,h,label,mem⟩
  have rel := (S.edges e).relation_at_hole label S.left_closed
  obtain ⟨i,eq⟩ := (S.context.mem_source_iff_port e S.token.2).mp mem
  apply none rel i
  exact (S.context.sourcePort_label e i).symm.trans (eq ▸ S.term)
end Specimen

/-- This is operational input safety for the constructed copying specimen
system, for arbitrary cost parameters and arbitrary allowed context classes. -/
theorem Specimens.inputSafe_of_no_term_inputs (T : PreTemplate) (none : T.NoTermInputs)
    (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (closed : T.OutputClosed) (Q P : CostOrder) :
    (system T Allowed closed).InputSafe Q P := by
  intro S _ _ _ entering
  exact False.elim (S.not_entering none entering)

namespace BoxPermutation
/-- The literal Figure 21 pair, with the paper's focus-free side condition. -/
def template : PreTemplate where
  Rel G H := UpToIso G H ∧ FocusFree G
  focus_free h := ⟨h.2,(h.1.allLabels _).mp h.2⟩

theorem template_no_term_inputs : template.NoTermInputs := by
  intro d I O G H rel
  obtain ⟨step,free⟩ := rel
  cases step with
  | witness f step g =>
    cases step with
    | permute B p =>
      intro i
      have eq : i = 0 := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
      subst i
      change Wire.thunk _ ≠ Wire.term
      intro eq; cases eq

theorem template_outputClosed : template.OutputClosed := template_no_term_inputs.outputClosed

/-- Both Q and its converse are covered, without a cost restriction. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P :=
  Specimens.inputSafe_of_no_term_inputs template template_no_term_inputs Allowed template_outputClosed Q P
end BoxPermutation
end Hypernets.Copying

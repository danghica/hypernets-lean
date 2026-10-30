import Hypernets.Copying.ParametricityLabels
import Hypernets.Copying.ParametricityEntry
import Hypernets.Copying.TemplateInputSafety

/-! Figure 20's complete literal pre-template, with independently arbitrary
finite family sizes and arbitrary original term sharing tree. No robustness
or observational equivalence is included as a premise or constructor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined

inductive Literal : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop where
  | families {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
      Literal (left d C) (right d m₁ m₂)

inductive Pair : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (literal : Literal A B) (right : DeepIso B H) : Pair G H

theorem Literal.closed {d I O} {G H : Hypernet d I O} (pair : Literal G H) :
    (FocusFree G ∧ HoleFree G) ∧ (FocusFree H ∧ HoleFree H) := by
  cases pair with
  | families d C => exact ⟨labels_closed (left_labels d C),labels_closed (right_labels _ _ _)⟩

theorem Pair.closed {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    (FocusFree G ∧ HoleFree G) ∧ (FocusFree H ∧ HoleFree H) := by
  cases pair with
  | witness f pair g =>
    exact ⟨⟨(allLabels_iso_iff _ f).mpr pair.closed.1.1,(allLabels_iso_iff _ f).mpr pair.closed.1.2⟩,
      ⟨(allLabels_iso_iff _ g).mp pair.closed.2.1,(allLabels_iso_iff _ g).mp pair.closed.2.2⟩⟩

/-- No private term or atom wire escapes the complete family and its store. -/
theorem Pair.noOutputs {d I O} {G H : Hypernet d I O} (pair : Pair G H) : O = [] := by
  cases pair with
  | witness _ pair _ => cases pair; rfl

def template : PreTemplate where
  Rel := Pair
  focus_free pair := ⟨pair.closed.1.1,pair.closed.2.1⟩

theorem literal {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
    template.Rel (left d C) (right d m₁ m₂) :=
  .witness (DeepIso.refl _) (.families d C) (DeepIso.refl _)

/-- Output closure follows from the actual empty interface; it places no
assumption on callback behavior or on the surrounding observing context. -/
theorem template_outputClosed : template.OutputClosed := by
  intro d I O G H pair
  cases pair.noOutputs
  left
  rw [oneWay_iff_paths]
  intro i j
  exact Fin.elim0 j

/-- Every original entry returns in one search transition on both sides,
including independently renamed graph carriers. -/
theorem Pair.returns {d I O} {G H : Hypernet d I O} (pair : Pair G H) (i : Fin I.length) :
    Search.Step G (.search,.input i) (.backtrack,.input i) ∧
      Search.Step H (.search,.input i) (.backtrack,.input i) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | families d C =>
      exact ⟨(Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step ((left_lambdaInputs d C).returns i),
        (Search.ofBoundaryIso (BoundaryIso.ofDeepIso g)).step ((right_lambdaInputs _ _ _).returns i)⟩

/-- Input safety uses the same one-step return on both sides and relocates
the shared token to backtracking. All original specimens and context classes
are permitted, without any plugging-closure assumption. -/
theorem template_inputSafe (Allowed : ∀ d, Hypernet d [.term] [] → Prop) (Q P : CostOrder) :
    (Specimens.system template Allowed template_outputClosed).InputSafe Q P := by
  intro S _ _ mode entering
  change S.token.1 = .search at mode
  obtain ⟨e,h,label,mem⟩ := entering
  have pair := (S.edges e).relation_at_hole label S.left_closed
  obtain ⟨i,eq⟩ := (S.context.mem_source_iff_port e S.token.2).mp mem
  have token : S.token = (.search,S.context.sourcePort e i) := Prod.ext mode eq.symm
  let D := S.relocate (.backtrack,S.token.2) S.term
  have l : UnboundedStep S.leftState D.leftState := by
    apply UnboundedStep.lift
    apply Combined.Step.search
    change Search.Step _ (Search.Expansion.position S.context S.left S.token)
      (Search.Expansion.position S.context S.left (.backtrack,S.token.2))
    rw [token]
    exact Search.expand_insert S.context S.left e (pair.returns i).1
  have r : UnboundedStep S.rightState D.rightState := by
    apply UnboundedStep.lift
    apply Combined.Step.search
    change Search.Step _ (Search.Expansion.position S.context S.right S.token)
      (Search.Expansion.position S.context S.right (.backtrack,S.token.2))
    rw [token]
    exact Search.expand_insert S.context S.right e (pair.returns i).2
  right; left
  exact ⟨D,0,1,Or.inl rfl,Q.refl 1,
    .cons (StateClass.project l) (.zero _),.cons (StateClass.project r) (.zero _)⟩

end Hypernets.Copying.Parametricity

import Hypernets.Copying.MixedBetaResidual

/-! Nested/mixed bodies, arbitrary padding, a stable lambda head, and actual
beta under a host containing an independent nontrivial residual contribution. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.BetaResidualExamples
open Graph Combined ResidualExamples

def argument : Hypernet 5 [.term] [] := primitiveNet 5 (.operation (.const .unit))
def argumentWitness : FillingWitness template argument argument :=
  .refl _ (Stable.constant 5 .unit).focusFree

/-- The mixed body certificate from the copying milestone now survives opening. -/
noncomputable def residual := closedBody.betaAfter template_paddingClosed argumentWitness

theorem mixed_opening :
    (Combined.machine 5 [.term] []).Steps 6
      ⟨Application.before closedRightBody argument,(.search,.input 0)⟩
      ⟨Application.after closedRightBody argument,(.search,.input 0)⟩ :=
  (DeepBeta.opening closedBody argumentWitness (Stable.constant 5 .unit)).2.1

/-- Padding does not restrict the number or depth of residual occurrences. -/
noncomputable def padded_residual (n : Nat) := residual.pad template_paddingClosed n

/-- A passive lambda head is stable even when its thunk output is attached to
an arbitrary callback by a surrounding context. The full lambda box is not a stable argument. -/
theorem lambda_argument_opening :
    (Combined.machine 2 [.term] (environmentInterface 1 0 ++ [.thunk 1])).Steps 6
      ⟨Application.before (k := 1) (h := 0) (O := [.thunk 1]) (lambdaPayload seed) (primitiveNet 2 (.operation .lam)),(.search,.input 0)⟩
      ⟨Application.after (k := 1) (h := 0) (O := [.thunk 1]) (lambdaPayload seed) (primitiveNet 2 (.operation .lam)),(.search,.input 0)⟩ :=
  (DeepBeta.opening leaf (.refl _ (Stable.lambda 2).focusFree) (Stable.lambda 2)).1

def omega : Term 1 0 := .app (.lam (.app (.var 0) (.var 0))) (.lam (.app (.var 0) (.var 0)))

/-- This exposes a self-application body in six steps, without asserting anything
about termination of its continuation. It uses the unchanged term translation. -/
theorem self_application_opening :
    (Combined.machine 2 [.term] []).Steps 6
      ⟨Application.before (Translation.term omega) (primitiveNet 2 (.operation (.const .unit))),(.search,.input 0)⟩
      ⟨Application.after (Translation.term omega) (primitiveNet 2 (.operation (.const .unit))),(.search,.input 0)⟩ :=
  by
  exact Combined.application_run (Application.opening_run (d := 1) (k := 0) (h := 0) (O := [])
    (Translation.term omega) _ (Stable.constant 2 .unit))

/-- These are deliberately different graphs in the other, unselected host slot. -/
def outsideLeft := CopyRule.after (ContractionTree.canonical .term 1) (lambdaPayload closedLeftBody)
def outsideRight := CopyRule.after (ContractionTree.canonical .term 1) (lambdaPayload closedRightBody)
noncomputable def outsideWitness : FillingWitness template outsideLeft outsideRight :=
  closedBody.deepCopy (ContractionTree.canonical .term 1)

def host : Hypernet 5 [.term] [] :=
  Serial.net (primitiveNet 5 (.operation (.binary .add)))
    (Net.Tensor.net (primitiveNet 5 (.hole ⟨20,[.term],[]⟩)) (primitiveNet 5 (.hole ⟨21,[.term],[]⟩)))
def selected : host.Edge := ⟨true,⟨false,(0 : Fin 1)⟩⟩

def family (P R : Hypernet 5 [.term] []) (e : host.Edge) :
    Hypernet 5 ((alphabet 5).signature.input (host.edgeLabel e))
      ((alphabet 5).signature.output (host.edgeLabel e)) := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact Net.corolla (alphabet 5).signature (primitiveLabel 5 (.operation (.binary .add)))
  · obtain ⟨b,e⟩ := e
    cases b
    · exact P
    · exact R

def familyWitness {P Q R S : Hypernet 5 [.term] []}
    (active : FillingWitness template P Q) (outside : FillingWitness template R S)
    (e : host.Edge) : FillingWitness template (family P R e) (family Q S e) := by
  obtain ⟨b,e⟩ := e
  cases b
  · exact .refl _ (by intro e m eq; cases eq)
  · obtain ⟨b,e⟩ := e
    cases b
    · exact active
    · exact outside

theorem others (P Q R : Hypernet 5 [.term] []) (e : host.Edge) (different : e ≠ selected) :
    family P R e = family Q R e := by
  obtain ⟨b,e⟩ := e
  cases b
  · rfl
  · obtain ⟨b,e⟩ := e
    cases b
    · exact False.elim (different (by congr; exact Fin.ext (by omega)))
    · rfl

theorem filled_closed {P R : Hypernet 5 [.term] []} (hp : HoleFree P) (hr : HoleFree R) :
    HoleFree (host.expand (family P R)) := by
  apply Serial.allLabels_expand
  rintro ⟨b,e⟩
  cases b
  · intro e h eq; cases eq
  · obtain ⟨b,e⟩ := e
    cases b
    · exact hp
    · exact hr

theorem token_internal : ¬ (host.sourcePort selected (0 : Fin 1)).IsInput := by
  intro h; cases h

def frameSource (B : Hypernet 4 [.term] (environmentInterface 1 0)) (R : Hypernet 5 [.term] []) : UnboundedState :=
  let F := family (Application.before B argument) R
  ⟨5,host.expand F,(.rewrite,Net.Expansion.host host F (host.sourcePort selected (0 : Fin 1)))⟩
def frameTarget (B : Hypernet 4 [.term] (environmentInterface 1 0)) (R : Hypernet 5 [.term] []) : UnboundedState :=
  let F := family (Application.after B argument) R
  ⟨5,host.expand F,(.search,Net.Expansion.host host F (host.sourcePort selected (0 : Fin 1)))⟩

/-- A selected deep beta redex and a genuinely independent certified contribution
are assembled in the same original coordinate specimen. -/
theorem hosted_diamond :
    UnboundedStep (frameSource closedLeftBody outsideLeft) (frameTarget closedLeftBody outsideLeft) ∧
    UnboundedStep (frameSource closedRightBody outsideRight) (frameTarget closedRightBody outsideRight) ∧
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState (frameTarget closedLeftBody outsideLeft))
      (StateClass.ofState (frameTarget closedRightBody outsideRight)) := by
  have h := FillingWitness.framed_rewrite host
    (family (Application.before closedLeftBody argument) outsideLeft)
    (family (Application.before closedRightBody argument) outsideRight)
    (family (Application.after closedLeftBody argument) outsideLeft)
    (family (Application.after closedRightBody argument) outsideRight)
    selected (others _ _ _) (others _ _ _) (0 : Fin 1) rfl
    (.local (.beta closedLeftBody argument (Stable.constant 5 .unit)))
    (.local (.beta closedRightBody argument (Stable.constant 5 .unit)))
    (familyWitness residual outsideWitness) template_outputClosed
    (filled_closed (Application.after_labels _ _ _ closed_body_closed.1 (Stable.constant 5 .unit).holeFree)
      (CopyRule.holeFree_after _ _ (DeepCopy.payload_closed closed_body_closed.1)))
    (filled_closed (Application.after_labels _ _ _ closed_body_closed.2 (Stable.constant 5 .unit).holeFree)
      (CopyRule.holeFree_after _ _ (DeepCopy.payload_closed closed_body_closed.2)))
  exact ⟨.lift h.1,.lift h.2.1,h.2.2⟩

theorem hosted_robust_case (Q P R : CostOrder) {u}
    (next : StateClass.machine.step (StateClass.ofState (frameSource closedLeftBody outsideLeft)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (frameSource closedRightBody outsideRight)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R (StateClass.project hosted_diamond.1)
    (StateClass.project hosted_diamond.2.1) hosted_diamond.2.2 next

theorem hosted_converse_case (Q P R : CostOrder) {u}
    (next : StateClass.machine.step (StateClass.ofState (frameSource closedRightBody outsideRight)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (frameSource closedLeftBody outsideLeft)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R (StateClass.project hosted_diamond.2.1)
    (StateClass.project hosted_diamond.1) (FillingWitness.quasi_exchange _ hosted_diamond.2.2) next
end Hypernets.Copying.BoxPermutation.BetaResidualExamples

import Hypernets.Copying.SharingTreeRequests
import Hypernets.Copying.NullaryRobustness

/-! The original input-safety clause follows from one-step sharing requests
and actual matched compute steps, including matched stuck rewrite states. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- Exact one-step matching at all original rewrite specimens, including
entered specimens. Both directions keep the original template orientation. -/
def PreTemplate.StepMatching (T : PreTemplate) (closed : T.OutputClosed) : Prop :=
  ∀ S : Specimen T Specimens.allContexts,
    StateClass.Rooted (StateClass.ofState S.leftState) →
    StateClass.Rooted (StateClass.ofState S.rightState) → S.token.1 = .rewrite →
      (∀ {s}, StateClass.machine.step (StateClass.ofState S.leftState) s →
        ∃ t, StateClass.machine.step (StateClass.ofState S.rightState) t ∧
          (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t) ∧
      (∀ {t}, StateClass.machine.step (StateClass.ofState S.rightState) t →
        ∃ s, StateClass.machine.step (StateClass.ofState S.leftState) s ∧
          (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t)

/-- Equality of the actual representation classes gives equivalence up to
any reflexive cost comparison on each residual endpoint. -/
theorem FillingWitness.quasi_equiv {S : SpecimenSystem StateClass.machine}
    {s t : StateClass} (pair : S.Quasi Eq Eq s t) (P : CostOrder) :
    S.Quasi (StateClass.machine.Equiv P) (StateClass.machine.Equiv P) s t := by
  intro leftRoot rightRoot
  obtain ⟨c,mode,lc,rc,left,right⟩ := pair leftRoot rightRoot
  refine ⟨c,mode,lc,rc,?_,?_⟩
  · rw [left]
    exact ⟨Machine.Refines.refl P _,Machine.Refines.refl P _⟩
  · rw [right]
    exact ⟨Machine.Refines.refl P _,Machine.Refines.refl P _⟩

/-- Every entered term tree first requests copying. Either both requests get
stuck, or both perform one actual matching rewrite with an admissible residual.
Thus the precise costs are respectively one/one or two/two. -/
theorem PreTemplate.StepMatching.inputSafe {T : PreTemplate} {closed : T.OutputClosed}
    (matching : T.StepMatching closed) (trees : T.SharingTrees) (Q P : CostOrder) :
    (Specimens.system T Specimens.allContexts closed).InputSafe Q P := by
  intro S leftRoot rightRoot mode entering
  change S.token.1 = .search at mode
  change S.Entering at entering
  change StateClass.Rooted (StateClass.ofState S.leftState) at leftRoot
  change StateClass.Rooted (StateClass.ofState S.rightState) at rightRoot
  let D := S.relocate (.rewrite,S.token.2) S.term
  obtain ⟨leftRequest,rightRequest⟩ := S.sharing_requests trees mode entering
  change StateClass.machine.step (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) at leftRequest
  change StateClass.machine.step (StateClass.ofState S.rightState) (StateClass.ofState D.rightState) at rightRequest
  have leftRootD := StateClass.rooted_step leftRoot leftRequest
  have rightRootD := StateClass.rooted_step rightRoot rightRequest
  obtain ⟨forward,backward⟩ := matching D leftRootD rightRootD rfl
  classical
  by_cases next : ∃ s, StateClass.machine.step (StateClass.ofState D.leftState) s
  · obtain ⟨s,leftStep⟩ := next
    obtain ⟨t,rightStep,residual⟩ := forward leftStep
    right; right
    exact ⟨1,1,s,t,Q.refl 2,
      .cons leftRequest (.cons leftStep (.zero _)),
      .cons rightRequest (.cons rightStep (.zero _)),FillingWitness.quasi_equiv residual P⟩
  · left
    have leftNormal : StateClass.machine.Normal (StateClass.ofState D.leftState) :=
      fun s step => next ⟨s,step⟩
    have rightNormal : StateClass.machine.Normal (StateClass.ofState D.rightState) := by
      intro t step
      obtain ⟨s,leftStep,_⟩ := backward step
      exact next ⟨s,leftStep⟩
    refine ⟨1,1,StateClass.ofState D.leftState,StateClass.ofState D.rightState,
      .cons leftRequest (.zero _),⟨leftNormal,?_⟩,
      .cons rightRequest (.zero _),⟨rightNormal,?_⟩⟩
    · intro final
      change Focus.rewrite = .backtrack ∧ _ at final
      cases final.1
    · intro final
      change Focus.rewrite = .backtrack ∧ _ at final
      cases final.1

/-- Matched actual steps also give full forward robustness, for every cost
triple and every supplied original representation-class successor. -/
theorem PreTemplate.StepMatching.robust {T : PreTemplate} {closed : T.OutputClosed}
    (matching : T.StepMatching closed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts closed).Robust Q P U := by
  intro S leftRoot rightRoot mode _ successor step
  change S.token.1 = .rewrite at mode
  obtain ⟨forward,_⟩ := matching S leftRoot rightRoot mode
  obtain ⟨t,right,residual⟩ := forward step
  right
  exact FillingWitness.matching_robust_case Q P U step right residual step

/-- Converse robustness uses the independently proved opposite matching
steps while retaining the actual original specimen and residual orientation. -/
theorem PreTemplate.StepMatching.robust_converse {T : PreTemplate} {closed : T.OutputClosed}
    (matching : T.StepMatching closed) (Q P U : CostOrder) :
    (Specimens.system T Specimens.allContexts closed).opposite.Robust Q P U := by
  intro S rightRoot leftRoot mode _ successor step
  change S.token.1 = .rewrite at mode
  obtain ⟨_,backward⟩ := matching S leftRoot rightRoot mode
  obtain ⟨s,left,residual⟩ := backward step
  right
  exact FillingWitness.matching_robust_case Q P U step left
    (FillingWitness.quasi_exchange _ residual) step

end Hypernets.Copying

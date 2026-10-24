import Hypernets.Graph.UAMClassDeterminism

/-! The complete UAM on recursive focus-preserving graph-isomorphism classes. -/
namespace Hypernets.Linear
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace UAMClasses
variable (B : Behaviour ops d kind)

/-- A class transition has actual representatives making one concrete UAM step.
No representative is selected, and no extra computation rule is introduced. -/
def Step (s t : DeepStateClass ops d) : Prop :=
  ∃ a b : State ops d, s = DeepStateClass.ofState a ∧ t = DeepStateClass.ofState b ∧ UAM.Step B a b

/-- Every named transition projects to a class transition. -/
theorem project {s t : State ops d} (step : UAM.Step B s t) :
    Step B (DeepStateClass.ofState s) (DeepStateClass.ofState t) := ⟨s,t,rfl,rfl,step⟩

/-- Equality of source classes suffices for equality of successor classes. -/
theorem deterministic (invariant : B.RespectsIso) (det : DeterministicModulo B.step)
    {s t u : DeepStateClass ops d} (left : Step B s t) (right : Step B s u) : t = u := by
  obtain ⟨a,b,sa,tb,left⟩ := left
  obtain ⟨c,e,sc,ue,right⟩ := right
  obtain ⟨iso⟩ := Quotient.exact (sa.symm.trans sc)
  exact tb.trans ((Quotient.sound (UAM.iso_deterministic B invariant det iso left right)).trans ue.symm)

/-- Finality is invariant under representatives, so final classes have no successor. -/
theorem final_normal {s t : DeepStateClass ops d} (final : DeepStateClass.Final s) : ¬ Step B s t := by
  rintro ⟨a,b,sa,_,step⟩
  rw [sa] at final
  exact UAM.final_normal B final step

/-- The full class machine, with the same boundary finality as the search machine. -/
def machine : Machine (DeepStateClass ops d) where
  step := Step B
  final := DeepStateClass.Final
  final_normal := final_normal B

/-- Concrete refocusing descends to the class machine. -/
theorem rooted_step (refocusing : RefocusingStates kind B.step)
    {s t : DeepStateClass ops d} (root : DeepStateClass.Rooted kind s) (step : Step B s t) :
    DeepStateClass.Rooted kind t := by
  obtain ⟨a,b,sa,tb,step⟩ := step
  rw [sa] at root
  rw [tb]
  exact UAM.refocusing B refocusing root step

/-- Projection preserves exact run length, including zero-step runs. -/
theorem project_steps {n} {s t : State ops d} (run : (UAM.machine B).Steps n s t) :
    (machine B).Steps n (DeepStateClass.ofState s) (DeepStateClass.ofState t) := by
  induction run with
  | zero => exact .zero _
  | cons step _ ih => exact .cons (project B step) ih

/-- Recursive search is included in the full class relation. -/
theorem search {s t : State ops d} (step : State.DeepSearch kind s t) :
    Step B (DeepStateClass.ofState s) (DeepStateClass.ofState t) := by
  obtain ⟨u,h,⟨iso⟩⟩ := State.deepSearch_iff.mp step
  have eq : DeepStateClass.ofState u = DeepStateClass.ofState t := Quotient.sound ⟨iso⟩
  exact ⟨s,u,rfl,eq.symm,.inl (.inl h)⟩

/-- At any specified non-rewrite source representative, a class transition
can be reflected to recursive search from that very representative. -/
theorem search_of_nonrewrite {s : State ops d} {t : DeepStateClass ops d}
    (mode : s.focussed.mode ≠ .rewrite) (step : Step B (DeepStateClass.ofState s) t) :
    ∃ u : State ops d, t = DeepStateClass.ofState u ∧ State.DeepSearch kind s u := by
  obtain ⟨a,b,sa,tb,step⟩ := step
  obtain ⟨iso⟩ := Quotient.exact sa
  rcases (UAM.step_iff B).mp step with search | rewrite
  · exact ⟨b,tb,State.deepSearch_source_iso (State.search_deepSearch search) iso.symm⟩
  · exact False.elim (mode (iso.mode.trans (UAM.rewrite_modes B rewrite).1))

/-- Every execution of the full class machine preserves rootedness. -/
theorem rooted_steps (refocusing : RefocusingStates kind B.step)
    {n s t} (run : (machine B).Steps n s t) (root : DeepStateClass.Rooted kind s) :
    DeepStateClass.Rooted kind t := by
  induction run with
  | zero => exact root
  | cons step _ ih => exact ih (rooted_step B refocusing root step)
end UAMClasses
end Hypernets.Linear

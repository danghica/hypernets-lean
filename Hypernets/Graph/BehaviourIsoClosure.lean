import Hypernets.Graph.ClassSafety

/-! Closing extrinsic behaviour under graph names does not add class transitions. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

/-- Computation shape is independent of names at all box depths. -/
theorem State.Compute.rename {s t u v : State ops d} (step : State.Compute kind s t)
    (a : Focussed.DeepIso s.focussed u.focussed) (b : Focussed.DeepIso t.focussed v.focussed) :
    State.Compute kind u v := by
  obtain ⟨sm,tm,e,o,label,active,source⟩ := step
  refine ⟨a.mode.symm.trans sm,b.mode.symm.trans tm,a.graph.edges.toFun e,o,
    labelEquiv_primitive (a.graph.edge_label e) (.operation o) label,active,?_⟩
  rw [← a.graph.source,source,List.map_cons,List.map_nil,a.target]

namespace Behaviour
variable (B : Behaviour ops d kind)
/-- Saturate only the supplied compute rules by recursive endpoint renaming. -/
def isoClosure : Behaviour ops d kind where
  step s t := ∃ a b, B.step a b ∧ Nonempty (Focussed.DeepIso a.focussed s.focussed) ∧
    Nonempty (Focussed.DeepIso b.focussed t.focussed)
  compute := by
    rintro s t ⟨a,b,h,⟨l⟩,⟨r⟩⟩
    exact (B.compute h).rename l r

/-- Every original extrinsic rule belongs to its closure. -/
theorem into_isoClosure {s t} (step : B.step s t) : B.isoClosure.step s t :=
  ⟨s,t,step,⟨Focussed.DeepIso.refl _⟩,⟨Focussed.DeepIso.refl _⟩⟩

/-- The closure is invariant under any independent recursive endpoint renaming. -/
theorem isoClosure_invariant : B.isoClosure.RespectsIso := by
  rintro s t u v a b ⟨x,y,h,⟨l⟩,⟨r⟩⟩
  exact ⟨x,y,h,⟨l.trans a⟩,⟨r.trans b⟩⟩

/-- Saturating the behaviour changes names only, not the full class relation. -/
theorem isoClosure_class_step {s t : DeepStateClass ops d} :
    UAMClasses.Step B.isoClosure s t ↔ UAMClasses.Step B s t := by
  constructor
  · rintro ⟨a,b,sa,tb,h⟩
    rcases h with intrinsic | ⟨x,y,h,⟨l⟩,⟨r⟩⟩
    · exact ⟨a,b,sa,tb,.inl intrinsic⟩
    · have ls : DeepStateClass.ofState x = DeepStateClass.ofState a := Quotient.sound ⟨l⟩
      have rs : DeepStateClass.ofState y = DeepStateClass.ofState b := Quotient.sound ⟨r⟩
      exact ⟨x,y,sa.trans ls.symm,tb.trans rs.symm,.inr h⟩
  · rintro ⟨a,b,sa,tb,intrinsic | ext⟩
    · exact ⟨a,b,sa,tb,.inl intrinsic⟩
    · exact ⟨a,b,sa,tb,.inr (B.into_isoClosure ext)⟩
end Behaviour
end Hypernets.Linear

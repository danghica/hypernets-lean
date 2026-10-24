import Hypernets.Graph.ConcreteSpecimenSystem

/-! Comparing UAM transitions whose sources differ by recursive renaming. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

namespace Substitution.Presentation
/-- A presentation's source may be renamed recursively without changing its reduct. -/
def renameSource {s t u : State ops d} (p : Presentation s t)
    (a : Focussed.DeepIso s.focussed u.focussed) : Presentation u t :=
  { p with left := by obtain ⟨b⟩ := p.left; exact ⟨b.trans a⟩ }
end Substitution.Presentation

namespace State
/-- Substitution reducts agree even when their source names differ inside boxes. -/
theorem substitution_iso_deterministic {s t u v : State ops d}
    (left : Substitution s t) (right : Substitution u v)
    (a : Focussed.DeepIso s.focussed u.focussed) :
    Nonempty (Focussed.DeepIso t.focussed v.focussed) := by
  obtain ⟨l⟩ := Linear.Substitution.presentation left
  obtain ⟨r⟩ := Linear.Substitution.presentation right
  exact (l.renameSource a).deterministic r

/-- Source exclusivity survives recursive renaming, by incidence uniqueness. -/
theorem substitution_compute_iso_exclusive {s t u v : State ops d}
    (sub : Substitution s t) (comp : Compute kind u v)
    (a : Focussed.DeepIso s.focussed u.focussed) : False := by
  obtain ⟨e,label,source⟩ := substitution_variable sub
  obtain ⟨_,_,f,o,fl,_,fs⟩ := comp
  have vl : u.graph.edgeLabel (a.graph.edges.toFun e) = primitiveLabel ops d .variable :=
    labelEquiv_primitive (a.graph.edge_label e) .variable label
  have vs : u.graph.source (a.graph.edges.toFun e) = [u.focussed.target] := by
    rw [← a.graph.source,source,List.map_cons,List.map_nil,a.target]
  have eq := u.graph.source_unique (v := u.focussed.target)
    (by rw [vs]; simp) (by rw [fs]; simp)
  have bad := primitiveLabel_injective d (vl.symm.trans ((congrArg u.graph.edgeLabel eq).trans fl))
  cases bad
end State

namespace Behaviour
/-- A behaviour defined on graph classes is independent of representative names
in both arguments. This is not a determinism or locality assumption. -/
def RespectsIso (B : Behaviour ops d kind) : Prop :=
  ∀ {s t u v}, Focussed.DeepIso s.focussed u.focussed →
    Focussed.DeepIso t.focussed v.focussed → B.step s t → B.step u v
end Behaviour

namespace UAM
variable (B : Behaviour ops d kind)
/-- Determinism modulo isomorphism extends from equal to isomorphic sources,
provided the extrinsic behaviour respects graph isomorphism. -/
theorem iso_deterministic (invariant : B.RespectsIso) (det : DeterministicModulo B.step)
    {s t u v : State ops d} (a : Focussed.DeepIso s.focussed u.focussed)
    (left : Step B s t) (right : Step B u v) :
    Nonempty (Focussed.DeepIso t.focussed v.focussed) := by
  have exclude {x y z w : State ops d} (b : Focussed.DeepIso x.focussed z.focussed)
      (search : State.Search kind x y) (rewrite : Rewrite B z w) : False :=
    State.search_not_rewrite search (b.mode.trans (rewrite_modes B rewrite).1)
  rcases (step_iff B).mp left with search | sub | ext
  · rcases (step_iff B).mp right with search' | rewrite
    · exact State.deepSearch_deterministic
        (State.deepSearch_source_iso (State.search_deepSearch search) a)
        (State.search_deepSearch search')
    · exact False.elim (exclude a search rewrite)
  · rcases (step_iff B).mp right with search | sub' | ext
    · exact False.elim (exclude a.symm search (.inl sub))
    · exact State.substitution_iso_deterministic sub sub' a
    · exact False.elim (State.substitution_compute_iso_exclusive sub (B.compute ext) a)
  · rcases (step_iff B).mp right with search | sub | ext'
    · exact False.elim (exclude a.symm search (.inr ext))
    · exact False.elim (State.substitution_compute_iso_exclusive sub (B.compute ext) a.symm)
    · exact det (invariant a (Focussed.DeepIso.refl _) ext) ext'
end UAM
end Hypernets.Linear

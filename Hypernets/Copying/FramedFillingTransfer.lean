import Hypernets.Copying.FillingSpecimens

/-! An actual local rewrite pair lifts through a shared host while arbitrary
other recursive template contributions are retained in the residual specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph Combined
universe u
variable {T : PreTemplate}

/-- The copying and opening residual interfaces use this transfer law. Other
components may contribute shallow pairs, deep pairs, or both. Only the selected
component changes during each of the two original machine transitions. -/
theorem framed_rewrite {d} (C : Hypernet d [.term] [])
    (G H K L : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (othersLeft : ∀ f, f ≠ e → G f = K f) (othersRight : ∀ f, f ≠ e → H f = L f)
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length)
    (term : ((alphabet d).signature.input (C.edgeLabel e))[i] = .term)
    {v : (G e).Vertex} {z : (H e).Vertex}
    (left : Rewrite (G e) v (K e) (.input i)) (right : Rewrite (H e) z (L e) (.input i))
    (w : ∀ f, FillingWitness T (K f) (L f)) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand K)) (rightClosed : HoleFree (C.expand L)) :
    Step ⟨C.expand G,(.rewrite,Net.Expansion.insert C G e v)⟩
      ⟨C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩ ∧
    Step ⟨C.expand H,(.rewrite,Net.Expansion.insert C H e z)⟩
      ⟨C.expand L,(.search,Net.Expansion.host C L (C.sourcePort e i))⟩ ∧
    (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq
      (StateClass.ofState ⟨d,C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩)
      (StateClass.ofState ⟨d,C.expand L,(.search,Net.Expansion.host C L (C.sourcePort e i))⟩) :=
  ⟨.rewrite (.expand C G K e othersLeft left),.rewrite (.expand C H L e othersRight right),
    expanded_quasi C w closed leftClosed rightClosed .search (C.sourcePort e i)
      ((C.sourcePort_label e i).trans term) (by intro eq; cases eq)⟩

/-- Equality-up-to residuals discharge the precise refinement-up-to clause
used by robustness, for any two cost preorders. -/
theorem quasi_refines {State : Type u} {M : Machine State} (S : SpecimenSystem M)
    {s t : State} (pair : S.Quasi Eq Eq s t) (P R : CostOrder) :
    S.Quasi (M.Refines P) (M.Refines R) s t := by
  intro hs ht
  obtain ⟨c,mode,lroot,rroot,left,right⟩ := pair hs ht
  refine ⟨c,mode,lroot,rroot,?_,?_⟩
  · rw [left]; exact Machine.Refines.refl P _
  · rw [right]; exact Machine.Refines.refl R _

/-- Exchanging the same specimen's projections reverses an equality-up-to
residual, including the order of the two rootedness conditions. -/
theorem quasi_exchange {State : Type u} {M : Machine State} (S : SpecimenSystem M)
    {s t : State} (pair : S.Quasi Eq Eq s t) : S.opposite.Quasi Eq Eq t s := by
  intro ht hs
  obtain ⟨c,mode,lc,rc,left,right⟩ := pair hs ht
  exact ⟨c,mode,rc,lc,right.symm,left.symm⟩

/-- A matched one-step pair with an equality-up-to residual gives the complete
robustness conclusion for that case, including any independently presented left
successor. Determinism here is the proved class-machine theorem. -/
theorem matching_robust_case {S : SpecimenSystem StateClass.machine} (Q P R : CostOrder)
    {s t u v : StateClass} (left : StateClass.machine.step s u) (right : StateClass.machine.step t v)
    (residual : S.Quasi Eq Eq u v) {u'} (step : StateClass.machine.step s u') :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u' a ∧
      StateClass.machine.Steps l t b ∧
      S.Quasi (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b := by
  have eq := StateClass.machine_deterministic step left
  subst u'
  exact ⟨0,1,u,v,Q.refl 1,.zero _,.cons right (.zero _),quasi_refines S residual P R⟩
end Hypernets.Copying.FillingWitness

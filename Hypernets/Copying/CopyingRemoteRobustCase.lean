import Hypernets.Copying.CopyingRemoteHost
import Hypernets.Copying.FramedFillingTransfer

/-! Actual two-sided copying residuals discharge both precise robustness
clauses, including arbitrary independently represented supplied successors.
Only previously proved exact sharing semantics supplies the refinements. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.TwoSidedResidual
open Graph Combined

theorem quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : TwoSidedResidual G v H w) (closed : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  obtain ⟨S,mode,sl,sr,l,r⟩ := p.quasi_equiv closed typed lroot rroot
  exact ⟨S,mode,sl,sr,
    l.1.mono (fun {n m} eq => by cases eq; exact P.refl n),
    r.1.mono (fun {n m} eq => by cases eq; exact U.refl n)⟩

theorem opposite_quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : TwoSidedResidual G v H w) (closed : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  intro rroot lroot
  obtain ⟨S,mode,sl,sr,l,r⟩ := p.quasi_equiv closed typed lroot rroot
  exact ⟨S,mode,sr,sl,
    r.2.mono (fun {n m} eq => by cases eq; exact P.refl n),
    l.2.mono (fun {n m} eq => by cases eq; exact U.refl n)⟩

/-- Two actual original rewrites and the original residual support any
supplied left successor, by the already proved quotient-machine determinism. -/
theorem matching_robust_case {d} {G H A B : Hypernet d [.term] []} {v w a b}
    (p : TwoSidedResidual A a B b) (left : Rewrite G v A a) (right : Rewrite H w B b)
    (closed : HoleFree G) (Q P U : CostOrder) {successor}
    (step : StateClass.machine.step (StateClass.ofState ⟨d,G,(.rewrite,v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,H,(.rewrite,w)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have same := StateClass.machine_deterministic step (StateClass.project (.lift (.rewrite left)))
  rw [same]
  exact ⟨0,1,_,_,Q.refl 1,.zero _,
    .cons (StateClass.project (.lift (.rewrite right))) (.zero _),
    p.quasi (rewrite_holeFree left closed) (rewrite_endpoints_term left).2 P U⟩

/-- The same directed original specimen supports any supplied right
successor; the exact sharing comparisons reverse their own directions. -/
theorem converse_matching_robust_case {d} {G H A B : Hypernet d [.term] []} {v w a b}
    (p : TwoSidedResidual A a B b) (left : Rewrite G v A a) (right : Rewrite H w B b)
    (closed : HoleFree G) (Q P U : CostOrder) {successor}
    (step : StateClass.machine.step (StateClass.ofState ⟨d,H,(.rewrite,w)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l (StateClass.ofState ⟨d,G,(.rewrite,v)⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have same := StateClass.machine_deterministic step (StateClass.project (.lift (.rewrite right)))
  rw [same]
  exact ⟨0,1,_,_,Q.refl 1,.zero _,
    .cons (StateClass.project (.lift (.rewrite left))) (.zero _),
    p.opposite_quasi (rewrite_holeFree left closed) (rewrite_endpoints_term left).2 P U⟩

end Hypernets.Copying.CopyingTemplate.TwoSidedResidual

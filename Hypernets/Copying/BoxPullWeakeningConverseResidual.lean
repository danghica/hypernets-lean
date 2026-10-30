import Hypernets.Copying.BoxPullWeakeningForwardRobustness

/-! Reverse use of a constructed BPullW residual. Exact Idem corrections
supply the left refinement of the original opposite quasi-specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.Residual
open Graph Combined

/-- The same genuine residual supports the opposite specimen orientation;
only the independently proved exact Idem corrections reverse direction. -/
theorem opposite_quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : Residual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  intro rroot lroot
  have midClosed : HoleFree p.middle :=
    (p.paired.filling.allLabels_iff (T := template) _ (fun pair => pair.allLabels _)).mp left
  have nextClosed : HoleFree p.next := p.first.idem_holeFree.mp midClosed
  have nextRoot := (p.second.idem_rooted_iff nextClosed).mpr rroot
  have midRoot := (p.first.idem_rooted_iff midClosed).mpr nextRoot
  have midTyped := p.paired.labels.symm.trans typed
  have nextTyped := p.first.labels.symm.trans midTyped
  have one := p.first.idem_exact midClosed midTyped midRoot
  have two := p.second.idem_exact nextClosed nextTyped nextRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ :=
    p.paired.quasi template_outputClosed left midClosed typed lroot midRoot
  refine ⟨S,mode,sr,sl,?_,?_⟩
  · change StateClass.machine.Refines P _
      ((Specimens.system template Specimens.allContexts template_outputClosed).right S)
    rw [r]
    exact (two.1.2.trans one.1.2).mono (fun {n m} eq => by cases eq; exact P.refl n)
  · change StateClass.machine.Refines U
      ((Specimens.system template Specimens.allContexts template_outputClosed).left S) _
    rw [← l]; exact Machine.Refines.refl U _

end Hypernets.Copying.BoxPullWeakening.Residual

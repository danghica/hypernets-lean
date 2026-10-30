import Hypernets.Copying.BoxPullContractionForwardRobustness

/-! Reverse use of a constructed BPullC residual. The exact sharing correction
supplies the left refinement of the original opposite quasi-specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.Residual
open Graph Combined

/-- The same genuine residual supports the opposite specimen orientation;
only the independently proved exact sharing correction reverses direction. -/
theorem opposite_quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : Residual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,H,(.search,w)⟩) (StateClass.ofState ⟨d,G,(.search,v)⟩) := by
  intro rroot lroot
  have midClosed : HoleFree p.middle :=
    (p.paired.filling.allLabels_iff (T := template) _ (fun pair => pair.allLabels _)).mp left
  have midRoot := (p.correction.sharing_rooted_iff midClosed).mpr rroot
  have midTyped := p.paired.labels.symm.trans typed
  have correction := p.correction.sharing_exact midClosed midTyped midRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ :=
    p.paired.quasi template_outputClosed left midClosed typed lroot midRoot
  refine ⟨S,mode,sr,sl,?_,?_⟩
  · change StateClass.machine.Refines P _
      ((Specimens.system template Specimens.allContexts template_outputClosed).right S)
    rw [r]
    exact correction.1.2.mono (fun {n m} eq => by cases eq; exact P.refl n)
  · change StateClass.machine.Refines U
      ((Specimens.system template Specimens.allContexts template_outputClosed).left S) _
    rw [← l]; exact Machine.Refines.refl U _

end Hypernets.Copying.BoxPullContraction.Residual

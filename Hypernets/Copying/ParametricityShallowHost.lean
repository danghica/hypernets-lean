import Hypernets.Copying.ParametricityReadDiagram
import Hypernets.Copying.ParametricityBareApplySource
import Hypernets.Copying.ParametricityRobustnessAssembly

/-! A constructed bare family diagram lifts through the exact original
application-and-hole cut. The callback and every other original filling
remain in its computed complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ShallowHost
open Graph Opening Combined
variable {d b} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (app : Occurrence (primitiveNet (d+1) (.operation .app)) C)
    (labels : ∀ x, C.edgeLabel (app.edges x) = primitiveLabel (d+1) (.operation .app))
    (e : C.Edge) (name : Nat)
    (label : C.edgeLabel e = primitiveLabel (d+1) (.hole ⟨name,List.replicate (b+1) .term,[]⟩))
    (j : Fin (b+1))
    (link : app.ports (.output (0 : Fin 2)) = C.sourcePort e
      ⟨j.val,by rw [label,primitive_input];simp [primitiveSignature]⟩)

def leftPart : Hypernet (d+1) (List.replicate (b+1) .term) [] :=
  (L e).reboundary (by rw [label,primitive_input];rfl) (by rw [label,primitive_output];rfl)

def rightPart : Hypernet (d+1) (List.replicate (b+1) .term) [] :=
  (R e).reboundary (by rw [label,primitive_input];rfl) (by rw [label,primitive_output];rfl)

/-- The actual original application is unchanged on both filling sides;
its primitive label discharges the retained-corolla premise. -/
noncomputable def appCopies (x : (primitiveNet (d+1) (.operation .app)).Edge) :
    LabelCopy (L (app.edges x)) (primitiveLabel (d+1) (.operation .app)) ×
      LabelCopy (R (app.edges x)) (primitiveLabel (d+1) (.operation .app)) := by
  obtain ⟨l,r⟩ := Classical.choice ((cert (app.edges x)).primitive_copies (labels x)
    (by intro h eq;cases eq))
  exact ⟨⟨l.edge,l.edge_label.trans (labels x),l.source,l.target,l.only⟩,
    ⟨r.edge,r.edge_label.trans (labels x),r.source,r.target,r.only⟩⟩

noncomputable abbrev footprint := BareApplyAt.Context.occurrence C app e name label j link

noncomputable def leftSourceIso : DeepIso
    ((CommonContextCut.skeleton C (footprint C app e name label j link)).expand
      (CommonContextCut.localFamily C (footprint C app e name label j link) L))
    (BareApplyAt.net (leftPart C e name label (L := L)) j) :=
  BareApplyAt.Context.sourceIso name j _ C app e label link L
    (fun x => (appCopies C cert app labels x).1) (DeepIso.refl _)

noncomputable def rightSourceIso : DeepIso
    ((CommonContextCut.skeleton C (footprint C app e name label j link)).expand
      (CommonContextCut.localFamily C (footprint C app e name label j link) R))
    (BareApplyAt.net (rightPart C e name label (R := R)) j) :=
  BareApplyAt.Context.sourceIso name j _ C app e label link R
    (fun x => (appCopies C cert app labels x).2) (DeepIso.refl _)

variable {n : Nat}
    (diagram : ReadDiagram
      (BareApplyAt.net (leftPart C e name label (L := L)) j) (.input ⟨0,by simp⟩)
      (BareApplyAt.net (rightPart C e name label (R := R)) j) (.input ⟨0,by simp⟩) n)

/-- Both actual source isomorphisms transport the entire already proved
opening/run/correction package, fixing the active input exactly. -/
noncomputable def localDiagram : ReadDiagram
    ((CommonContextCut.skeleton C (footprint C app e name label j link)).expand
      (CommonContextCut.localFamily C (footprint C app e name label j link) L)) (.input ⟨0,by simp⟩)
    ((CommonContextCut.skeleton C (footprint C app e name label j link)).expand
      (CommonContextCut.localFamily C (footprint C app e name label j link) R)) (.input ⟨0,by simp⟩) n :=
  diagram.congr (leftSourceIso C cert app labels e name label j link).symm
    (rightSourceIso C cert app labels e name label j link).symm

variable (free : FocusFree C) (leftClosed : HoleFree (C.expand L))
    (leftRoot : Search.RootedFrom (C.expand L) 0
      (.rewrite,Net.Expansion.host C L (app.ports (.input (0 : Fin 1)))))
    (rightRoot : Search.RootedFrom (C.expand R) 0
      (.rewrite,Net.Expansion.host C R (app.ports (.input (0 : Fin 1)))))
include cert labels link diagram free leftClosed leftRoot rightRoot

/-- The actual original host realizes the forward quantitative clause once
the selected original family's concrete read diagram has been supplied. -/
theorem forward_case (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,
        (.rewrite,Net.Expansion.host C L (app.ports (.input (0 : Fin 1))))⟩) successor) :
    RobustnessAssembly.ForwardClause C (R := R) (app.ports (.input (0 : Fin 1))) U successor := by
  let p := localDiagram C cert app labels e name label j link diagram
  have point := BareApplyAt.Context.input C app e name label j link
  have lr := point.symm ▸ leftRoot
  have rr := point.symm ▸ rightRoot
  have actual := point.symm ▸ step
  have result := BetaHost.forward_case C (footprint C app e name label j link) cert free
    leftClosed lr rr p.left p.right p.run p.correction p.paired p.typed U actual
  simpa only [point] using result

/-- The same actual original source pair gives the converse inequality for
every independently supplied right successor, retaining the full correction. -/
theorem converse_case (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,
        (.rewrite,Net.Expansion.host C R (app.ports (.input (0 : Fin 1))))⟩) successor) :
    RobustnessAssembly.ConverseClause C (L := L) (app.ports (.input (0 : Fin 1))) P successor := by
  let p := localDiagram C cert app labels e name label j link diagram
  have point := BareApplyAt.Context.input C app e name label j link
  have lr := point.symm ▸ leftRoot
  have rr := point.symm ▸ rightRoot
  have actual := point.symm ▸ step
  have result := BetaHost.converse_case C (footprint C app e name label j link) cert free
    leftClosed lr rr p.left p.right p.run p.correction p.paired p.typed P actual
  simpa only [point] using result

end Hypernets.Copying.Parametricity.ShallowHost

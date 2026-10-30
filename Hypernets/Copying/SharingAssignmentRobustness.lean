import Hypernets.Copying.SharingAssignmentSource
import Hypernets.Copying.SharingAssignmentSelection
import Hypernets.Copying.SharingBasinLocalIso
import Hypernets.Copying.CommonContextRobustness

/-! Every original assignment match admits the maximal sharing-context diagram,
with literal paired assignment rewrites and an original-template residual specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Opening Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert trees free closed leftClosed rightClosed

/-- An arbitrary supplied assignment successor satisfies the full quantitative
robustness clause. The maximal original sharing component, its inactive inputs,
and the actual residual specimen are constructed from the supplied occurrence. -/
theorem assignment_matching {n K} (A : ContractionTree .atom (n+1))
    (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Occurrence (Assignment.before A G) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (Assignment.inputPort n K 0) = Net.Expansion.host C L token)
    : ∃ x y,
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) x ∧
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) y ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq x y := by
  obtain ⟨S,labels,a,rest,u,vvalue,o,nd,boundary,rl,il,sl,rs,rt,is,it,ss,st,vi⟩ :=
    assignment_selection C cert trees leftClosed A G stable f attached
  let value := assignment_value C cert trees leftClosed A G stable f
  let tree := SharingBasin.occurrence (s := .atom) S labels (a::rest) nd boundary
  have sharing (e) : SharingLabel d .atom (C.edgeLabel (tree.edges e)) := labels e.val e.property
  have ti : tree.ports (.input ⟨0,by simp⟩) = a.val := rfl
  have to : tree.ports (.output 0) = S.output := rfl
  have disjoint := Assignment.Context.components_disjoint C tree value
    (f.edges (Assignment.beforeAssign A G)).1 (f.edges (Assignment.beforeInstance A G)).1
    (f.edges (Assignment.beforeStore A G)).1 rl il sl u vvalue rt is vi stable sharing
  let c := Assignment.Context.occurrence C tree value
    (f.edges (Assignment.beforeAssign A G)).1 (f.edges (Assignment.beforeInstance A G)).1
    (f.edges (Assignment.beforeStore A G)).1 rl il sl token u a.val vvalue S.output o
    rs rt is it ss st ti to vi disjoint
  let X := SharingBasin.leftTree (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed
  let Y := SharingBasin.rightTree (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed
  let w := (SharingBasin.treeWitness (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed).sharingAssignmentAfter (FillingWitness.refl G stable.focusFree)
  have leftIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (Assignment.before X G) :=
    Assignment.Context.sourceIso C cert tree value stable
      (f.edges (Assignment.beforeAssign A G)).1 (f.edges (Assignment.beforeInstance A G)).1
      (f.edges (Assignment.beforeStore A G)).1 rl il sl token u a.val vvalue S.output o
      rs rt is it ss st ti to vi disjoint X
      (SharingBasin.localLeftIso (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed)
  have rightIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (Assignment.before Y G) :=
    Assignment.Context.sourceIso C (fun e => (cert e).converse) tree value stable
      (f.edges (Assignment.beforeAssign A G)).1 (f.edges (Assignment.beforeInstance A G)).1
      (f.edges (Assignment.beforeStore A G)).1 rl il sl token u a.val vvalue S.output o
      rs rt is it ss st ti to vi disjoint Y
      (SharingBasin.localRightIso (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed)
  have left : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (.input ⟨0,by simp [Assignment.inputs]⟩) (Assignment.after X G)
      (.input ⟨0,by simp [Assignment.inputs]⟩) := by
    have step : Rewrite (Assignment.before X G) (Assignment.inputPort rest.length K 0)
        (Assignment.after X G) (Assignment.inputPort rest.length K 0) := .local (.assign X G stable)
    simpa only [Assignment.inputPort,Port.map,Fin.val_zero] using step.rename leftIso.symm (DeepIso.refl _)
  have right : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (.input ⟨0,by simp [Assignment.inputs]⟩) (Assignment.after Y G)
      (.input ⟨0,by simp [Assignment.inputs]⟩) := by
    have step : Rewrite (Assignment.before Y G) (Assignment.inputPort rest.length K 0)
        (Assignment.after Y G) (Assignment.inputPort rest.length K 0) := .local (.assign Y G stable)
    simpa only [Assignment.inputPort,Port.map,Fin.val_zero] using step.rename rightIso.symm (DeepIso.refl _)
  let q : w.context.Vertex := .input ⟨0,by simp [Assignment.inputs]⟩
  have typed : w.context.vertexLabel q = .term := rfl
  have entry : c.ports (.input ⟨0,by simp [Assignment.inputs]⟩) = token := rfl
  obtain ⟨ls,rs,residual⟩ := CommonContextCut.diamond C c cert free w
    (a := .input ⟨0,by simp [Assignment.inputs]⟩) q typed
    (by simpa only [q,FillingWitness.leftPosition_input,Net.Expansion.host,Port.map] using left)
    (by simpa only [q,FillingWitness.rightPosition_input,Net.Expansion.host,Port.map] using right)
    closed leftClosed rightClosed
  refine ⟨_,_,?_,?_,residual⟩
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite ls))
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite rs))

/-- The precise quantitative robustness clause follows for any independently
supplied successor by the already proved complete-machine determinism. -/
theorem assignment_robust_case {n K} (A : ContractionTree .atom (n+1))
    (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Occurrence (Assignment.before A G) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (Assignment.inputPort n K 0) = Net.Expansion.host C L token)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨x,y,left,right,residual⟩ := assignment_matching C cert trees free closed leftClosed rightClosed A G stable f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

end Hypernets.Copying.MaximalSharing

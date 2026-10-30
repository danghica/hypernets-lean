import Hypernets.Copying.SharingSameSource
import Hypernets.Copying.SharingSameSelection
import Hypernets.Copying.SharingBasinLocalIso
import Hypernets.Copying.CommonContextRobustness

/-! Every original same-store equality match admits the maximal sharing-context diagram,
with literal paired equality rewrites and an original-template residual specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Opening Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
include cert trees free closed leftClosed rightClosed

/-- An arbitrary supplied equality successor satisfies the full quantitative
robustness clause. The maximal original sharing component, its inactive inputs,
and the actual residual specimen are constructed from the supplied occurrence. -/
theorem same_matching {n} (A : ContractionTree .atom (n+2))
    (f : Occurrence (AtomEquality.Same.before A d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort n 0) = Net.Expansion.host C L token)
    : ∃ x y,
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) x ∧
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) y ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq x y := by
  obtain ⟨S,labels,a,b,rest,u,u',o,nd,boundary,rl,il,jl,sl,rs,rt,is,it,js,jt,ss,st⟩ :=
    same_selection C cert trees A f attached
  let tree := SharingBasin.occurrence (s := .atom) S labels (a::b::rest) nd boundary
  have sharing (e) : SharingLabel d .atom (C.edgeLabel (tree.edges e)) := labels e.val e.property
  have ti : tree.ports (.input ⟨0,by simp⟩) = a.val := rfl
  have tj : tree.ports (.input ⟨1,by simp⟩) = b.val := rfl
  have to : tree.ports (.output 0) = S.output := rfl
  have distinct : (f.edges (AtomEquality.Same.beforeLeft A d)).1 ≠ (f.edges (AtomEquality.Same.beforeRight A d)).1 := by
    intro eq
    have same : u = u' := List.cons.inj (is.symm.trans ((congrArg C.source eq).trans js)) |>.1
    have nd := C.target_nodup (f.edges ⟨.compare,(0 : Fin 1)⟩).1
    rw [rt,same] at nd
    simp at nd
  let c := AtomEquality.Same.Context.occurrence C tree
    (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Same.beforeLeft A d)).1
    (f.edges (AtomEquality.Same.beforeRight A d)).1
    (f.edges (AtomEquality.Same.beforeStore A d)).1 rl il jl sl token u u' a.val b.val S.output o
    rs rt is it js jt ss st ti tj to distinct sharing
  let X := SharingBasin.leftTree (s := .atom) C cert trees S labels (a::b::rest) nd boundary leftClosed
  let Y := SharingBasin.rightTree (s := .atom) C cert trees S labels (a::b::rest) nd boundary leftClosed
  let w := (SharingBasin.treeWitness (s := .atom) C cert trees S labels (a::b::rest) nd boundary leftClosed).sharingSameAfter
  have leftIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (AtomEquality.Same.before X d) :=
    AtomEquality.Same.Context.sourceIso C cert tree
      (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Same.beforeLeft A d)).1
      (f.edges (AtomEquality.Same.beforeRight A d)).1
    (f.edges (AtomEquality.Same.beforeStore A d)).1 rl il jl sl token u u' a.val b.val S.output o
      rs rt is it js jt ss st ti tj to distinct sharing X
      (SharingBasin.localLeftIso (s := .atom) C cert trees S labels (a::b::rest) nd boundary leftClosed)
  have rightIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (AtomEquality.Same.before Y d) :=
    AtomEquality.Same.Context.sourceIso C (fun e => (cert e).converse) tree
      (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Same.beforeLeft A d)).1
      (f.edges (AtomEquality.Same.beforeRight A d)).1
    (f.edges (AtomEquality.Same.beforeStore A d)).1 rl il jl sl token u u' a.val b.val S.output o
      rs rt is it js jt ss st ti tj to distinct sharing Y
      (SharingBasin.localRightIso (s := .atom) C cert trees S labels (a::b::rest) nd boundary leftClosed)
  have left : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (.input ⟨0,by simp [AtomEquality.Same.inputs]⟩) (AtomEquality.Same.after X d)
      (.input ⟨0,by simp [AtomEquality.Same.inputs]⟩) := by
    have step : Rewrite (AtomEquality.Same.before X d) (AtomEquality.Same.inputPort rest.length 0)
        (AtomEquality.Same.after X d) (AtomEquality.Same.inputPort rest.length 0) := .local (.same X d)
    simpa only [AtomEquality.Same.inputPort,Port.map,Fin.val_zero] using step.rename leftIso.symm (DeepIso.refl _)
  have right : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (.input ⟨0,by simp [AtomEquality.Same.inputs]⟩) (AtomEquality.Same.after Y d)
      (.input ⟨0,by simp [AtomEquality.Same.inputs]⟩) := by
    have step : Rewrite (AtomEquality.Same.before Y d) (AtomEquality.Same.inputPort rest.length 0)
        (AtomEquality.Same.after Y d) (AtomEquality.Same.inputPort rest.length 0) := .local (.same Y d)
    simpa only [AtomEquality.Same.inputPort,Port.map,Fin.val_zero] using step.rename rightIso.symm (DeepIso.refl _)
  let q : w.context.Vertex := .input ⟨0,by simp [AtomEquality.Same.inputs]⟩
  have typed : w.context.vertexLabel q = .term := rfl
  have entry : c.ports (.input ⟨0,by simp [AtomEquality.Same.inputs]⟩) = token := rfl
  obtain ⟨ls,rs,residual⟩ := CommonContextCut.diamond C c cert free w
    (a := .input ⟨0,by simp [AtomEquality.Same.inputs]⟩) q typed
    (by simpa only [q,FillingWitness.leftPosition_input,Net.Expansion.host,Port.map] using left)
    (by simpa only [q,FillingWitness.rightPosition_input,Net.Expansion.host,Port.map] using right)
    closed leftClosed rightClosed
  refine ⟨_,_,?_,?_,residual⟩
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite ls))
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite rs))

/-- The precise quantitative robustness clause follows for any independently
supplied successor by the already proved complete-machine determinism. -/
theorem same_robust_case {n} (A : ContractionTree .atom (n+2))
    (f : Occurrence (AtomEquality.Same.before A d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort n 0) = Net.Expansion.host C L token)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨x,y,left,right,residual⟩ := same_matching C cert trees free closed leftClosed rightClosed A f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

end Hypernets.Copying.MaximalSharing

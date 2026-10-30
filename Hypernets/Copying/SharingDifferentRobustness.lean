import Hypernets.Copying.SharingDifferentSource
import Hypernets.Copying.SharingDifferentSelection
import Hypernets.Copying.SharingBasinLocalIso
import Hypernets.Copying.CommonContextRobustness

/-! Every original different-store equality match admits the maximal sharing-context diagram,
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
theorem different_matching {n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1))
    (f : Occurrence (AtomEquality.Different.before A B d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L token)
    : ∃ x y,
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) x ∧
      StateClass.machine.step (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) y ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq x y := by
  obtain ⟨S,U,labels,labels',a,b,rest,rest',u,u',o,o',nd,boundary,nd',boundary',
      rl,il,jl,sl,tl,rs,rt,is,it,js,jt,ss,st,ts,tt,stores,disjoint⟩ :=
    different_selection C cert trees A B f attached
  let tree := SharingBasin.occurrence (s := .atom) S labels (a::rest) nd boundary
  let tree' := SharingBasin.occurrence (s := .atom) U labels' (b::rest') nd' boundary'
  have sharing (e) : SharingLabel d .atom (C.edgeLabel (tree.edges e)) := labels e.val e.property
  have sharing' (e) : SharingLabel d .atom (C.edgeLabel (tree'.edges e)) := labels' e.val e.property
  have ti : tree.ports (.input ⟨0,by simp⟩) = a.val := rfl
  have tj : tree'.ports (.input ⟨0,by simp⟩) = b.val := rfl
  have to : tree.ports (.output 0) = S.output := rfl
  have to' : tree'.ports (.output 0) = U.output := rfl
  have apart : ∀ e j, tree.edges e ≠ tree'.edges j := by
    intro e j eq
    change e.val = j.val at eq
    exact disjoint e.val ⟨e.property,eq.symm ▸ j.property⟩
  have distinct : (f.edges (AtomEquality.Different.beforeLeft A B d)).1 ≠ (f.edges (AtomEquality.Different.beforeRight A B d)).1 := by
    intro eq
    have same : u = u' := List.cons.inj (is.symm.trans ((congrArg C.source eq).trans js)) |>.1
    have nd := C.target_nodup (f.edges ⟨.compare,(0 : Fin 1)⟩).1
    rw [rt,same] at nd
    simp at nd
  let c := AtomEquality.Different.Context.occurrence C tree tree'
    (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Different.beforeLeft A B d)).1
    (f.edges (AtomEquality.Different.beforeRight A B d)).1
    (f.edges (AtomEquality.Different.beforeStore A B d)).1
    (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 rl il jl sl tl token u u' a.val b.val S.output U.output o o'
    rs rt is it js jt ss st ts tt ti tj to to' distinct stores sharing sharing' apart
  let X := SharingBasin.leftTree (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed
  let Y := SharingBasin.rightTree (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed
  let X' := SharingBasin.leftTree (s := .atom) C cert trees U labels' (b::rest') nd' boundary' leftClosed
  let Y' := SharingBasin.rightTree (s := .atom) C cert trees U labels' (b::rest') nd' boundary' leftClosed
  let w := (SharingBasin.treeWitness (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed).sharingDifferentAfter
    (SharingBasin.treeWitness (s := .atom) C cert trees U labels' (b::rest') nd' boundary' leftClosed)
  have leftIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (AtomEquality.Different.before X X' d) :=
    AtomEquality.Different.Context.sourceIso C cert tree tree'
      (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Different.beforeLeft A B d)).1
      (f.edges (AtomEquality.Different.beforeRight A B d)).1
    (f.edges (AtomEquality.Different.beforeStore A B d)).1
    (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 rl il jl sl tl token u u' a.val b.val S.output U.output o o'
      rs rt is it js jt ss st ts tt ti tj to to' distinct stores sharing sharing' apart X X'
      (SharingBasin.localLeftIso (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed)
      (SharingBasin.localLeftIso (s := .atom) C cert trees U labels' (b::rest') nd' boundary' leftClosed)
  have rightIso : DeepIso ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (AtomEquality.Different.before Y Y' d) :=
    AtomEquality.Different.Context.sourceIso C (fun e => (cert e).converse) tree tree'
      (f.edges ⟨.compare,(0 : Fin 1)⟩).1 (f.edges (AtomEquality.Different.beforeLeft A B d)).1
      (f.edges (AtomEquality.Different.beforeRight A B d)).1
    (f.edges (AtomEquality.Different.beforeStore A B d)).1
    (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 rl il jl sl tl token u u' a.val b.val S.output U.output o o'
      rs rt is it js jt ss st ts tt ti tj to to' distinct stores sharing sharing' apart Y Y'
      (SharingBasin.localRightIso (s := .atom) C cert trees S labels (a::rest) nd boundary leftClosed)
      (SharingBasin.localRightIso (s := .atom) C cert trees U labels' (b::rest') nd' boundary' leftClosed)
  have left : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c L))
      (.input ⟨0,by simp [AtomEquality.Different.inputs]⟩) (AtomEquality.Different.after X X' d)
      (.input ⟨0,by simp [AtomEquality.Different.inputs]⟩) := by
    have step : Rewrite (AtomEquality.Different.before X X' d) (AtomEquality.Different.inputPort rest.length rest'.length 0)
        (AtomEquality.Different.after X X' d) (AtomEquality.Different.inputPort rest.length rest'.length 0) := .local (.different X X' d)
    simpa only [AtomEquality.Different.inputPort,Port.map,Fin.val_zero] using step.rename leftIso.symm (DeepIso.refl _)
  have right : Rewrite ((CommonContextCut.skeleton C c).expand (CommonContextCut.localFamily C c R))
      (.input ⟨0,by simp [AtomEquality.Different.inputs]⟩) (AtomEquality.Different.after Y Y' d)
      (.input ⟨0,by simp [AtomEquality.Different.inputs]⟩) := by
    have step : Rewrite (AtomEquality.Different.before Y Y' d) (AtomEquality.Different.inputPort rest.length rest'.length 0)
        (AtomEquality.Different.after Y Y' d) (AtomEquality.Different.inputPort rest.length rest'.length 0) := .local (.different Y Y' d)
    simpa only [AtomEquality.Different.inputPort,Port.map,Fin.val_zero] using step.rename rightIso.symm (DeepIso.refl _)
  let q : w.context.Vertex := .input ⟨0,by simp [AtomEquality.Different.inputs]⟩
  have typed : w.context.vertexLabel q = .term := rfl
  have entry : c.ports (.input ⟨0,by simp [AtomEquality.Different.inputs]⟩) = token := rfl
  obtain ⟨ls,rs,residual⟩ := CommonContextCut.diamond C c cert free w
    (a := .input ⟨0,by simp [AtomEquality.Different.inputs]⟩) q typed
    (by simpa only [q,FillingWitness.leftPosition_input,Net.Expansion.host,Port.map] using left)
    (by simpa only [q,FillingWitness.rightPosition_input,Net.Expansion.host,Port.map] using right)
    closed leftClosed rightClosed
  refine ⟨_,_,?_,?_,residual⟩
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite ls))
  · simpa only [StateClass.machine,entry] using StateClass.project (.lift (.rewrite rs))

/-- The precise quantitative robustness clause follows for any independently
supplied successor by the already proved complete-machine determinism. -/
theorem different_robust_case {n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1))
    (f : Occurrence (AtomEquality.Different.before A B d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L token)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L token)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R token)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  obtain ⟨x,y,left,right,residual⟩ := different_matching C cert trees free closed leftClosed rightClosed A B f attached
  exact FillingWitness.matching_robust_case Q P U left right residual step

end Hypernets.Copying.MaximalSharing

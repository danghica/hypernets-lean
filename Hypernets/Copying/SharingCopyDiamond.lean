import Hypernets.Copying.SharingCopyContext
import Hypernets.Copying.SharingTreeResiduals
import Hypernets.Copying.CommonContextRobustness

/-! Actual local rewrites and original residual specimens for the complete
maximal sharing-tree/copyable-payload source, at the selected first input. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingCopyContext
open Graph Opening RetainedFootprint Combined
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Occurrence G (C.expand L))
    (S : C.RootedBasin Wire.term)
    (labels : ∀ e, S.chosen e → SharingBasin.Eligible C .term e)
    (a : S.Vertex) (rest : List S.Vertex) (distinct : (a::rest).Nodup)
    (boundary : ∀ v, v ∈ a::rest ↔ S.Input v)
    (join : S.output = port C f.matchEmbedding cert
      (SharingPayload.avoids C cert trees copyable f) (.input ⟨0,by simp⟩))
    (free : FocusFree C) (closed : HoleFree (C.expand L))

noncomputable abbrev leftTreeForCopy :=
  SharingBasin.leftTree (s := .term) C cert trees S labels (a::rest) distinct boundary closed
noncomputable abbrev rightTreeForCopy :=
  SharingBasin.rightTree (s := .term) C cert trees S labels (a::rest) distinct boundary closed
noncomputable abbrev rightPayload :=
  (payload C cert trees copyable f).expand
    (rightFamily C f cert (SharingPayload.avoids C cert trees copyable f))

/-- The actual post-copy specimen retains the entire residual sharing tree,
both independently filled payload copies, and the literal two-use distributors. -/
noncomputable def copyResidual : FillingWitness T
    (CopyRule.after (leftTreeForCopy C cert trees S labels a rest distinct boundary closed) G)
    (CopyRule.after (rightTreeForCopy C cert trees S labels a rest distinct boundary closed)
      (rightPayload C cert trees copyable f)) :=
  (SharingBasin.treeWitness (s := .term) C cert trees S labels (a::rest) distinct boundary closed).sharingCopyAfter
    (witness C f cert (SharingPayload.avoids C cert trees copyable f) free)
    (witness C f cert (SharingPayload.avoids C cert trees copyable f) free)

/-- The full normalized left common source performs the original copying
rule at the actual selected ordered input, without narrowing the rule. -/
theorem copy_left :
    Rewrite
      ((CommonContextCut.skeleton C
        (occurrence C cert trees copyable f S labels (a::rest) distinct boundary join)).expand
        (CommonContextCut.localFamily C
          (occurrence C cert trees copyable f S labels (a::rest) distinct boundary join) L))
      (.input ⟨0,by simp⟩)
      (CopyRule.after (leftTreeForCopy C cert trees S labels a rest distinct boundary closed) G)
      (.input ⟨0,by simp⟩) := by
  have step : Rewrite
      (CopyRule.before (leftTreeForCopy C cert trees S labels a rest distinct boundary closed) G)
      (.input ⟨0,by simp⟩) _ (.input ⟨0,by simp⟩) := .local (.copy _ G copyable)
  have mapped := step.rename
    (leftIso C cert trees copyable f S labels (a::rest) distinct boundary join closed).symm
    (DeepIso.refl _)
  simpa only [Port.map] using mapped

include free in
/-- The other actual payload remains copyable by the original recursive
filling laws; its local rewrite has the same selected-input coordinate. -/
theorem copy_right :
    Rewrite
      ((CommonContextCut.skeleton C
        (occurrence C cert trees copyable f S labels (a::rest) distinct boundary join)).expand
        (CommonContextCut.localFamily C
          (occurrence C cert trees copyable f S labels (a::rest) distinct boundary join) R))
      (.input ⟨0,by simp⟩)
      (CopyRule.after (rightTreeForCopy C cert trees S labels a rest distinct boundary closed)
        (rightPayload C cert trees copyable f))
      (.input ⟨0,by simp⟩) := by
  have copyableRight := (SharingPayload.paired C cert trees copyable f free).1
  have step : Rewrite
      (CopyRule.before (rightTreeForCopy C cert trees S labels a rest distinct boundary closed)
        (rightPayload C cert trees copyable f))
      (.input ⟨0,by simp⟩) _ (.input ⟨0,by simp⟩) := .local (.copy _ _ copyableRight)
  have mapped := step.rename
    (rightIso C cert trees copyable f S labels (a::rest) distinct boundary join closed).symm
    (DeepIso.refl _)
  simpa only [Port.map] using mapped

end Hypernets.Copying.SharingCopyContext

namespace Hypernets.Copying.SharingCopyContext
open Graph Opening Combined
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Occurrence G (C.expand L))
    (S : C.RootedBasin Wire.term)
    (labels : ∀ e, S.chosen e → SharingBasin.Eligible C .term e)
    (a : S.Vertex) (rest : List S.Vertex) (distinct : (a::rest).Nodup)
    (boundary : ∀ v, v ∈ a::rest ↔ S.Input v)
    (join : S.output = RetainedFootprint.port C f.matchEmbedding cert
      (SharingPayload.avoids C cert trees copyable f) (.input 0))
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))

include cert trees copyable f labels rest distinct boundary join free leftClosed rightClosed in
/-- The maximal copy diagram proves the full paper robustness clause for
any separately supplied successor, including a match using a smaller tree. -/
theorem copy_matching :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L a.val)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R a.val)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  let common := occurrence C cert trees copyable f S labels (a::rest) distinct boundary join
  let w := copyResidual C cert trees copyable f S labels a rest distinct boundary free leftClosed
  let q : w.context.Vertex := .input ⟨0,by simp⟩
  have typed : w.context.vertexLabel q = .term := by
    change (List.replicate (rest.length+1) Wire.term)[0] = Wire.term
    exact List.getElem_replicate _
  have entry : common.ports (.input ⟨0,by simp⟩) = a.val :=
    occurrence_input C cert trees copyable f S labels (a::rest) distinct boundary join ⟨0,by simp⟩
  obtain ⟨left,right,residual⟩ := CommonContextCut.diamond C common cert free w
    (a := .input ⟨0,by simp⟩) q typed
    (by simpa only [q,FillingWitness.leftPosition_input,Net.Expansion.host,Port.map] using
      copy_left C cert trees copyable f S labels a rest distinct boundary join leftClosed)
    (by simpa only [q,FillingWitness.rightPosition_input,Net.Expansion.host,Port.map] using
      copy_right C cert trees copyable f S labels a rest distinct boundary join free leftClosed)
    closed leftClosed rightClosed
  refine ⟨_,_,?_,?_,residual⟩
  · have h : StateClass.machine.step _ _ := StateClass.project (.lift (.rewrite left))
    simpa only [entry] using h
  · have h : StateClass.machine.step _ _ := StateClass.project (.lift (.rewrite right))
    simpa only [entry] using h

include cert trees copyable f labels rest distinct boundary join free leftClosed rightClosed in
/-- The maximal copy diagram proves the full paper robustness clause for
any separately supplied successor, including a match using a smaller tree. -/
theorem copy_robust_case (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L a.val)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R a.val)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  let common := occurrence C cert trees copyable f S labels (a::rest) distinct boundary join
  let w := copyResidual C cert trees copyable f S labels a rest distinct boundary free leftClosed
  let q : w.context.Vertex := .input ⟨0,by simp⟩
  have typed : w.context.vertexLabel q = .term := by
    change (List.replicate (rest.length+1) Wire.term)[0] = Wire.term
    exact List.getElem_replicate _
  have entry : common.ports (.input ⟨0,by simp⟩) = a.val :=
    occurrence_input C cert trees copyable f S labels (a::rest) distinct boundary join ⟨0,by simp⟩
  have result := CommonContextCut.robust_case C common cert free w
    (a := .input ⟨0,by simp⟩) (successor := successor) q typed
    (by simpa only [q,FillingWitness.leftPosition_input,Net.Expansion.host,Port.map] using copy_left C cert trees copyable f S labels a rest distinct boundary join leftClosed)
    (by simpa only [q,FillingWitness.rightPosition_input,Net.Expansion.host,Port.map] using copy_right C cert trees copyable f S labels a rest distinct boundary join free leftClosed)
    closed leftClosed rightClosed Q P U
  simpa only [entry] using result (by simpa only [entry] using step)

end Hypernets.Copying.SharingCopyContext

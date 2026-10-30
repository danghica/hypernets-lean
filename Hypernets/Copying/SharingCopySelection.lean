import Hypernets.Copying.SharingCopyDiamond
import Hypernets.Copying.CopyPayloadHead

/-! A real original copying occurrence determines its maximal common sharing
source. The selected port remains first and no rematching certificate is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Opening RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {n k h} (A : ContractionTree .term (n+1))
    {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Occurrence (CopyRule.before A G) (C.expand L))

noncomputable abbrev copyPayload := (Serial.rightOccurrence (A.atDepth d) G).comp f
noncomputable abbrev copyTree := (Serial.leftOccurrence (A.atDepth d) G).comp f

include cert trees copyable in
/-- Every real rooted copying source supplies a maximal original sharing
basin, with all original shallow holes and the exact payload junction intact. -/
theorem copy_selection {v : C.Vertex}
    (entry : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v)
    (reachable : Search.OperationReachable C v) :
    ∃ S : C.RootedBasin Wire.term,
      ∃ labels : ∀ e, S.chosen e → SharingBasin.Eligible C .term e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex,
        a.val = v ∧ (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        S.output = port C (copyPayload C A f).matchEmbedding cert
          (SharingPayload.avoids C cert trees copyable (copyPayload C A f)) (.input 0) := by
  obtain ⟨head,p,label,source,nonsharing,notHole⟩ := copyable.head
  let payload := copyPayload C A f
  let tree := copyTree C A f
  have actualLabel : (C.expand L).edgeLabel (payload.edges head) = primitiveLabel d p :=
    payload.matchEmbedding.primitive head p label
  have linked : tree.ports (.output 0) = payload.ports (.input 0) :=
    congrArg f.ports (Serial.occurrence_boundary (A.atDepth d) G 0)
  have actualSource : tree.ports (.output 0) ∈ (C.expand L).source (payload.edges head) := by
    rw [← payload.source,source]
    exact List.mem_map.mpr ⟨.input 0,List.mem_cons_self,linked.symm⟩
  have actualEntry : tree.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v := by
    change f.ports ((Serial.leftOccurrence (A.atDepth d) G).ports _) = _
    rw [Serial.leftOccurrence_input]
    exact entry
  obtain ⟨S,labels,a,rest,selected,distinct,boundary,out⟩ :=
    term_component C cert trees A tree actualLabel actualSource nonsharing notHole
      ⟨0,by simp⟩ actualEntry reachable
  refine ⟨S,labels,a,rest,selected,distinct,boundary,?_⟩
  apply Net.Expansion.host_injective C L
  exact out.trans (linked.trans
    (host_port C payload.matchEmbedding cert
      (SharingPayload.avoids C cert trees copyable payload) (.input 0)).symm)

end Hypernets.Copying.MaximalSharing

import Hypernets.Copying.BoxPullContractionReversePrimitive
import Hypernets.Copying.MinimalCopyOccurrence
import Hypernets.Copying.SharingTreeSerialJoin

/-! Converse copying rematches only the actually selected term spine. Its
side branches remain in the host complement; every selected contraction is
proved retained at the original common context, without binding restrictions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseCopy
open Graph Opening
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) {v : C.Vertex}
include cert closed

/-- The original input-to-root path supplies a complete retained smaller
contraction tree with the identical selected input and payload attachment. -/
theorem selected_tree {m} (T : ContractionTree .term (m+1))
    (f : Occurrence (T.atDepth d) (C.expand R))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v) :
    ∃ n orientation, ∃ g : Occurrence ((ContractionSpine.tree .term n orientation).atDepth d) (C.expand R),
      g.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v ∧
      g.ports (.output 0) = f.ports (.output 0) ∧
      RetainedFootprint.AvoidsShallow C g.matchEmbedding := by
  obtain ⟨n,orientation,small,input,output,a,source,paths⟩ := T.minimal_spine d ⟨0,by simp⟩
  let g := small.comp f
  have selected : Net.Expansion.host C R v ∈ (C.expand R).source (f.edges a) := by
    rw [← attached]
    exact f.matchEmbedding.source_mem source
  refine ⟨n,orientation,g,(congrArg f.ports input).trans attached,congrArg f.ports output,?_⟩
  intro e
  apply right_primitive_ancestry C cert closed f.matchEmbedding
    (BoxPermutation.PrimitiveFootprint.relabel T.net d) selected
  have liftPath {a b n} (path : Trace T.net.Adjacent a b n) : Ancestor (T.atDepth d) a b := by
    induction path with
    | refl a => exact .refl _
    | step adjacent path ih => exact .step adjacent ih
  exact liftPath (paths e)

/-- Both actual ordered serial components are available as full occurrences. -/
noncomputable def serialLeft {J K P} (A : Hypernet d J K) (B : Hypernet d K P) :
    Occurrence A (Serial.net A B) :=
  (MatchEmbedding.serialLeft A B).occurrence (fun e => by
    change LabelEquiv d _ ((Serial.net A B).edgeLabel (Serial.leftEdge A B e))
    rw [Serial.leftEdge_label]; exact labelEquiv_refl _ _)

omit cert closed in
/-- The shared serial junction is the same actual vertex on both sides. -/
theorem serial_boundary {J K P} (A : Hypernet d J K) (B : Hypernet d K P) (i : Fin K.length) :
    (serialLeft A B).ports (.output i) = (Occurrence.serialRight A B).ports (.input i) := by
  cases d <;> rfl

end Hypernets.Copying.BoxPullContraction.ReverseCopy

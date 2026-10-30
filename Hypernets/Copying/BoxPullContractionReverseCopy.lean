import Hypernets.Copying.BoxPullContractionReversePayload
import Hypernets.Copying.BoxPullContractionReverseLambda

/-! Actual converse copying enabledness for arbitrary recursive BPullC
fillings. The selected term spine and complete original copyable payload
are constructed from the supplied right rewrite. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseCopy
open Graph Opening
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R)) (free : FocusFree C) {v : C.Vertex}
include cert closed free

/-- Every actual copyable payload on the right has a complete original left
payload at the same incoming context wire. Lambda free interfaces may change
exactly as prescribed by the original box-pulling rule. -/
theorem reflect_copyable {k h} (A : Hypernet d [.term] (environmentInterface k h))
    (copyable : Copyable A) (f : Occurrence A (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ k' h', ∃ B : Hypernet d [.term] (environmentInterface k' h'), Copyable B ∧
      ∃ g : Occurrence B (C.expand L), g.ports (.input 0) = Net.Expansion.host C L v := by
  obtain ⟨A',⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
  let placed := (Occurrence.ofIso iso.symm).comp f
  have token : placed.ports (.input 0) = Net.Expansion.host C R v := attached
  cases normal with
  | plain d code =>
    obtain ⟨g,point⟩ := reflect_plain C cert closed code placed token
    exact ⟨_,_,_,(CopyRule.NormalForm.plain d code).copyable,g,point⟩
  | lambda B =>
    obtain ⟨k',h',B',g,point⟩ := ReverseLambda.reflectLambda C cert free closed B placed token
    exact ⟨k',h',lambdaPayload B',.lambda B',g,point⟩

/-- Every original right copying match is enabled on the original left.
The finite selected tree, original lambda body and interface, actual ordered
join and complete complement are all constructed from that supplied match. -/
theorem copying_enabled {m k h} (T : ContractionTree .term (m+1))
    (A : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable A)
    (f : Occurrence (CopyRule.before T A) (C.expand R))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v) :
    ∃ H : Hypernet d I O, ∃ w, Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  let originalTree := (serialLeft (T.atDepth d) A).comp f
  let value := (Occurrence.serialRight (T.atDepth d) A).comp f
  have treeInput : originalTree.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C R v := by
    change f.ports (BoundarySerial.leftInsert _ _ (.input _)) = _
    rw [Combined.left_input]
    exact attached
  obtain ⟨n,orientation,rightTree,input,output,avoid⟩ := selected_tree C cert closed T originalTree treeInput
  let U := ContractionSpine.tree .term n orientation
  let matched := RetainedFootprint.across C rightTree.matchEmbedding (fun e => (cert e).converse) avoid
  let leftTree : Occurrence (U.atDepth d) (C.expand L) :=
    matched.occurrence (matched.primitive_labels (BoxPermutation.PrimitiveFootprint.relabel U.net d))
  obtain ⟨q,root⟩ := RetainedFootprint.port_origin C rightTree.matchEmbedding
    (fun e => (cert e).converse) avoid (.output 0)
  change Net.Expansion.host C R q = rightTree.ports (.output 0) at root
  have valueInput : value.ports (.input 0) = Net.Expansion.host C R q := by
    rw [root,output]
    exact (congrArg f.ports (serial_boundary (T.atDepth d) A 0)).symm
  obtain ⟨k',h',B,copyB,g,point⟩ := reflect_copyable C cert closed free A copyable value valueInput
  have boundary : ∀ i, leftTree.ports (.output i) = g.ports (.input i) := by
    intro i
    change Fin 1 at i
    have zero : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    rw [point]
    exact RetainedFootprint.across_host C rightTree.matchEmbedding
      (fun e => (cert e).converse) avoid root.symm
  let joint := Occurrence.sharingCopyJoin U leftTree g copyB boundary
  have step := joint.local_rewrite (.copy U B copyB)
  have token : joint.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v := by
    dsimp only [joint,Occurrence.sharingCopyJoin]
    rw [Occurrence.SerialJoin.occurrence_input]
    exact RetainedFootprint.across_host C rightTree.matchEmbedding
      (fun e => (cert e).converse) avoid input
  rw [token] at step
  exact ⟨_,_,step⟩

end Hypernets.Copying.BoxPullContraction.ReverseCopy

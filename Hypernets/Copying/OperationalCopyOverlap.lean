import Hypernets.Copying.OperationalLeftLabels
import Hypernets.Copying.LocalRewriteOccurrence

/-! Forward copying footprints avoid every shallow original operational hole.
The complete original contraction tree is retained, including sibling edges
away from the selected spine; nested template occurrences under boxes remain
allowed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates
open Graph Search.Expansion Opening

namespace ForwardOverlap
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
include cert free away

/-- The normalized payload's entire original copy footprint avoids shallow
operational holes. Label exclusion handles every sharing-tree branch; binding
freedom handles the actual resolved primitive and boxed payload. -/
theorem normal_copy_avoids {n k h} (tree : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (normal : CopyRule.NormalForm H)
    (f : Occurrence (CopyRule.before tree H) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let matched := (CopyRule.localSuccessorMatch tree normal).map f
  have payload (e : H.Edge) (hole : Hole) :
      C.edgeLabel (f.edges (Serial.rightEdge (CopyRule.tree tree d) H e)).1 ≠
        primitiveLabel d (.hole hole) := by
    have aux (w : (C.expand L).Vertex) (eq : w = Net.Expansion.host C L v)
        (m : CopyRule.SuccessorMatch (C.expand L) w H) :
        C.edgeLabel (m.payload.edges e).1 ≠ primitiveLabel d (.hole hole) := by
      subst w
      exact BindingOverlap.copying_payload_not_hole C cert free away m e hole
    exact aux _ attached matched
  intro a hole
  obtain ⟨part,a⟩ := a
  cases part with
  | false =>
    cases d with
    | zero =>
      apply BindingOverlap.sharing_not_hole C cert .term
      rcases tree.labels a with label | label
      · exact .inl (f.matchEmbedding.primitive _ _ (congrArg (primitiveLabel 0) label))
      · exact .inr (f.matchEmbedding.primitive _ _ (congrArg (primitiveLabel 0) label))
    | succ d =>
      apply BindingOverlap.sharing_not_hole C cert .term
      rcases tree.labels a with label | label
      · exact .inl (f.matchEmbedding.primitive _ _ (congrArg (primitiveLabel (d+1)) label))
      · exact .inr (f.matchEmbedding.primitive _ _ (congrArg (primitiveLabel (d+1)) label))
  | true =>
    cases d <;> exact payload a hole

/-- Carrier normalization is used only in the proof. The resulting exclusion
is about every edge of the supplied original full-label occurrence and its
unchanged contraction-tree presentation. -/
theorem copy_avoids {n k h} (tree : ContractionTree .term (n+1))
    {H : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable H)
    (f : Occurrence (CopyRule.before tree H) (C.expand L))
    (attached : f.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  obtain ⟨K,⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
  let whole := CopyRule.before_congr (Net.Iso.refl tree.net) iso
  let normalized := (Occurrence.ofIso whole.symm).comp f
  have placed : normalized.ports (.input ⟨0,by simp⟩) = Net.Expansion.host C L v := attached
  have result := normal_copy_avoids C cert free away tree normal normalized placed
  intro a hole
  have avoids := result (whole.edges.toFun a) hole
  change C.edgeLabel (f.edges (whole.edges.invFun (whole.edges.toFun a))).1 ≠ _ at avoids
  rw [whole.edges.left_inv] at avoids
  exact avoids

/-- Every actual local copying derivation has a shallow-hole-free occurrence;
all other local constructors are excluded by their actual primitive head. -/
theorem local_copy_avoids {J K} {A B : Hypernet d J K} {a b}
    (step : Combined.Local A a B b)
    (head : ∃ e, MatchEmbedding.HeadAt A a e (.contraction .term))
    (f : Occurrence A (C.expand L))
    (attached : f.ports a = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  obtain ⟨e,head⟩ := head
  cases step with
  | copy tree H copyable => exact copy_avoids C cert free away tree copyable f attached
  | allocate G stable => cases (MatchEmbedding.head_unique head (Allocation.head_at G)).2
  | read T d => cases (MatchEmbedding.head_unique head (Dereference.localMatch T d).head).2
  | assign T G stable => cases (MatchEmbedding.head_unique head (Assignment.localMatch T G).head).2
  | same T d => cases (MatchEmbedding.head_unique head (AtomEquality.Same.head_at T d)).2
  | different T U d => cases (MatchEmbedding.head_unique head (AtomEquality.Different.head_at T U d)).2
  | beta B G stable => cases (MatchEmbedding.head_unique head (Application.localMatch B G).head_at).2
  | unaryArithmetic d n => cases (MatchEmbedding.head_unique head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d m n => cases (MatchEmbedding.head_unique head (Arithmetic.binary_head o d m n)).2

/-- Extract a genuine full-label local occurrence from any original contextual
copying rewrite, and prove the entire extracted footprint avoids every shallow
operational contribution. Plugging, expansion, carrier renaming, and arbitrary
sharing-tree presentations are all covered by the original rewrite derivation. -/
theorem copying_rewrite_occurrence {H : Hypernet d I O} {w}
    (step : Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w)
    (head : ∃ e, MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) e (.contraction .term)) :
    ∃ J K, ∃ A B : Hypernet d J K, ∃ a b, Combined.Local A a B b ∧
      ∃ f : Occurrence A (C.expand L), f.ports a = Net.Expansion.host C L v ∧
        RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := step.local_occurrence
  have mappedHead : ∃ e, MatchEmbedding.HeadAt (C.expand L) (f.ports a) e (.contraction .term) := by
    rw [attached]
    exact head
  have localHead := Combined.rewrite_head_exists_reflect (.local localStep) f.matchEmbedding mappedHead
  exact ⟨J,K,A,B,a,b,localStep,f,attached,
    local_copy_avoids C cert free away localStep localHead f attached⟩

end ForwardOverlap
end Hypernets.Copying.OperationalTemplates

import Hypernets.Copying.ParametricityReadCorrection
import Hypernets.Copying.ParametricityPrivateApplication

/-! Carry the constructed readback correction through the actual original
private-instance copying prefix and the stable-argument beta context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Combined Opening

namespace ReaderPrefix

theorem focusFree {d n O} (G : Hypernet d (List.replicate (n+1) .term) O)
    (free : FocusFree G) : FocusFree (net G) := by
  apply Serial.allLabels_expand
  intro b
  cases d <;> cases b
  all_goals first | exact free | (intro e m eq; cases eq)

end ReaderPrefix

namespace PrivateRead
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

theorem tail_focusFree : FocusFree (tail d) :=
  Serial.focusFree_net
    (Serial.focusFree_net (ContractionAlgebra.tree_focusFree (ContractionTree.canonical .atom 1) d)
      (by cases d <;> intro e m eq <;> cases eq))
    (by cases d <;> intro e m eq <;> cases eq)

theorem before_focusFree : FocusFree (before T d) :=
  Serial.focusFree_net (ReaderPrefix.focusFree _
    (CopyRule.before_allLabels (k := 0) (h := 1) (fun p => ∀ m, p ≠ .focus m) T (primitiveNet d .instanceEdge)
      (by cases d <;> intro e m eq <;> cases eq)
      (by intro m eq; cases eq) (by intro m eq; cases eq))) (tail_focusFree d)

theorem ready_focusFree : FocusFree (ready T d) :=
  Serial.focusFree_net (ReaderPrefix.focusFree _
    (CopyRule.focusFree_after (k := 0) (h := 1) T (primitiveNet d .instanceEdge)
      (by cases d <;> intro e m eq <;> cases eq))) (tail_focusFree d)

/-- This endpoint keeps the complete original complement of the matched
private read and inserts the reconstructed returned-value/store graph. -/
noncomputable def corrected : Hypernet d (List.replicate (n+1) .term) [] :=
  CompleteMatchCut.replaceWith (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label
    (ReadTail.Normal.net (ContractionSpine.tree .atom 2 orientation) d)

noncomputable def correctedPoint : (corrected T d).Vertex :=
  CompleteMatchCut.replacePort (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label
    (ReadTail.Normal.net (ContractionSpine.tree .atom 2 orientation) d)
    (.input ⟨0,by simp [Dereference.inputs]⟩)

theorem corrected_input : correctedPoint T d = .input ⟨0,by simp⟩ :=
  CompleteMatchCut.replace_input (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label
    ⟨0,by simp [Dereference.inputs]⟩ ⟨0,by simp⟩ (tail_token T d)

theorem after_input : (after T d).2.2 = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort _ _ _ (ReadTail.resume _ d) = _
  rw [ReadTail.resume_input]
  exact CompleteMatchCut.replace_input (tailOccurrence T d).matchEmbedding (tailOccurrence T d).label
    ⟨0,by simp [Dereference.inputs]⟩ ⟨0,by simp⟩ (tail_token T d)

/-- The original eight-transition private read ends at a genuinely certified
three-link residual, with its original token and unchanged complement. -/
noncomputable def correction : ReadCorrection (after T d).1 (after T d).2.2
    (corrected T d) (correctedPoint T d) := by
  let A := ContractionSpine.tree .atom 2 orientation
  have inner := ReadTail.originalReadCorrection A d
  rw [ReadTail.resume_input] at inner
  have lifted := ReadCorrection.cutInput (tailOccurrence T d) (ready_focusFree T d)
    ⟨0,by simp [Dereference.inputs]⟩ inner
  change ReadCorrection _ (CompleteMatchCut.replacePort _ _ _ (ReadTail.resume A d)) _ _
  simpa only [ReadTail.resume_input,A,corrected,correctedPoint] using lifted

theorem corrected_factorization :
    (machine d (List.replicate (n+1) .term) []).Steps 8
      ⟨before T d,(.search,.input ⟨0,by simp⟩)⟩ (after T d) ∧
    Nonempty (ReadCorrection (after T d).1 (after T d).2.2 (corrected T d) (correctedPoint T d)) :=
  ⟨run T d,⟨correction T d⟩⟩

end PrivateRead

namespace PrivateApplication
variable {d n O} (T : ContractionTree .term (n+1)) (V : Hypernet (d+1) [.term] O)

theorem opened_focusFree (free : FocusFree V) : FocusFree (opened T V) :=
  Translation.allLabels_tensor _ (PrivateRead.before_focusFree T (d+1))
    (Serial.focusFree_net (by intro e m eq; cases eq) free)

/-- The normalized private read is inserted into the original opened beta
context. In particular, every output of the discarded argument survives. -/
noncomputable def corrected :=
  CompleteMatchCut.replaceWith (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
    (PrivateRead.corrected T (d+1))

noncomputable def correctedPoint : (corrected T V).Vertex :=
  CompleteMatchCut.replacePort (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
    (PrivateRead.corrected T (d+1)) (.input ⟨0,by simp⟩)

noncomputable def correction (free : FocusFree V) :
    ReadCorrection
      (CompleteMatchCut.replaceState (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
        (PrivateRead.after T (d+1))).1
      (CompleteMatchCut.replaceState (privateOccurrence T V).matchEmbedding (privateOccurrence T V).label
        (PrivateRead.after T (d+1))).2.2
      (corrected T V) (correctedPoint T V) := by
  have p := PrivateRead.correction T (d+1)
  rw [PrivateRead.after_input,PrivateRead.corrected_input] at p
  have lifted := p.cutInput (privateOccurrence T V) (opened_focusFree T V free) ⟨0,by simp⟩
  change ReadCorrection _ (CompleteMatchCut.replacePort _ _ _ (PrivateRead.after T (d+1)).2.2) _ _
  simpa only [PrivateRead.after_input,corrected,correctedPoint] using lifted

/-- The original beta and private read perform exactly nine transitions.
Their actual endpoint is related to the retained store/value graph by the
constructed copying and garbage-collection chain, with its original focus. -/
theorem nine_transition_correction (stable : Stable V) :
    ∃ target, (machine (d+1) (List.replicate (n+1) .term ++ []) ([] ++ O)).Steps 9
      ⟨before T V,(.rewrite,token T V)⟩ target ∧ target.2.1 = .search ∧
      Nonempty (ReadCorrection target.1 target.2.2 (corrected T V) (correctedPoint T V)) := by
  obtain ⟨target,steps,⟨f⟩⟩ := run T V stable
  have p := (correction T V stable.focusFree).congr f.graph (DeepIso.refl _)
  have mode : target.2.1 = .search := f.mode.symm
  have vertex := f.vertex
  simp only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] at p
  rw [vertex] at p
  exact ⟨target,steps,mode,⟨p⟩⟩

end PrivateApplication
end Hypernets.Copying.Parametricity

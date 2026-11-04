import Hypernets.Copying.ParametricityBareApplyJoin
import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceCutBoundary
import Hypernets.Copying.RetainedBetaEnabled

/-! Reconstruct a closed selected abstraction and its untouched family by
inverting the actual complete occurrence of its opened body. The argument
is the external output wire and no argument edge enters this footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.RightBareApplicationCut
open Graph Opening Application
variable {d n I} (hi : I = List.replicate (n+1) Wire.term)
    (B : Hypernet (d+1) [.term] (environmentInterface 1 0))
    {G : Hypernet (d+2) I [.term]}
    (R : Hypernet (d+2) (List.replicate n .term) [])
    (f : Occurrence (openBody B) G) (r : Occurrence R G)
    (apart : ∀ e a, f.edges e ≠ r.edges a)

noncomputable abbrev target := CompleteMatchCut.replaceWith f.matchEmbedding f.label (RetainedFrame.net B)
noncomputable def inserted : Occurrence (RetainedFrame.net B) (target B f) := f.replacement (RetainedFrame.net B)
noncomputable def head := (RetainedFrame.appOccurrence B).comp (inserted B f)
noncomputable def selected := (RetainedFrame.closureOccurrence B).comp (inserted B f)
noncomputable def remaining := f.acrossCut r apart (RetainedFrame.net B)

def family : Hypernet (d+2) (List.replicate (n+1) .term) [] :=
  (Net.Tensor.net (lambdaPayload B) R).reboundary (by simp [List.replicate_succ]) rfl

theorem selected_remaining : ∀ e a, (selected B f).edges e ≠ (remaining B R f r apart).edges a := by
  intro e a eq; cases eq
noncomputable def familyOccurrence : Occurrence (family B R) (target B f) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected B f) (remaining B R f r apart)
    (selected_remaining B R f r apart)).reboundarySource _ _

theorem family_zero : (familyOccurrence B R f r apart).ports (.input ⟨0,by simp⟩) =
    (selected B f).ports (.input (0 : Fin 1)) := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected B f) (remaining B R f r apart) (selected_remaining B R f r apart)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft (lambdaPayload B) R).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head B f).ports (.output (0 : Fin 2)) =
    (familyOccurrence B R f r apart).ports (.input ⟨0,by simp⟩) := by rw [family_zero]; rfl

theorem head_family : ∀ e a, (head B f).edges e ≠ (familyOccurrence B R f r apart).edges a := by
  rintro e ⟨part,a⟩ eq
  cases part
  · obtain ⟨part,a⟩ := a
    cases part <;> cases eq
  · cases eq

noncomputable def occurrence : Occurrence ((BareApplyFirst.net (family B R)).reboundary hi.symm rfl) (target B f) :=
  (BareApplyFirst.Join.occurrence (family B R) (head B f) (familyOccurrence B R f r apart)
    (head_function B R f r apart) (head_family B R f r apart)).reboundarySource hi.symm rfl

variable (first : f.ports (.input (0 : Fin 1)) = .input ⟨0,by rw [hi];simp⟩)
    (rest : ∀ i : Fin n, r.ports (.input ⟨i.val,by simp⟩) = .input ⟨i.val+1,by rw [hi];simp⟩)
    (out : f.ports (.output 0) = .output 0)

include first in
theorem head_input : (head B f).ports (.input (0 : Fin 1)) = .input ⟨0,by rw [hi];simp⟩ := by
  change CompleteMatchCut.replacePort f.matchEmbedding f.label (RetainedFrame.net B) (.input (0 : Fin 1)) = _
  exact CompleteMatchCut.replace_input _ _ _ _ first

include rest in
theorem family_succ (i : Fin n) : (familyOccurrence B R f r apart).ports (.input ⟨i.val+1,by simp⟩) =
    .input ⟨i.val+1,by rw [hi];simp⟩ := by
  have eq := Occurrence.tensorJoin_right (selected B f) (remaining B R f r apart)
    (selected_remaining B R f r apart) (.input ⟨i.val,by simp⟩)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight (lambdaPayload B) R).ports (.input ⟨i.val,by simp⟩) =
      .input ⟨i.val+1,by simp⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))
  rw [represented] at eq
  exact eq.trans (f.acrossCut_input r apart (RetainedFrame.net B) (rest i))

include out in
theorem head_argument : (head B f).ports (.output (1 : Fin 2)) = .output 0 := by
  change CompleteMatchCut.replacePort f.matchEmbedding f.label (RetainedFrame.net B) (.output 0) = _
  change Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none _
    ((CompleteMatchCut.net f.matchEmbedding f.label).targetPort none (Fin.cast (congrArg List.length (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm) 0)) = _
  rw [CompleteMatchCut.hole_targetPort]
  have point : CompleteMatchCut.outputPort f.matchEmbedding 0 = .output 0 :=
    CompleteMatchCut.embed_injective f.matchEmbedding ((CompleteMatchCut.embed_output f.matchEmbedding 0).trans out)
  rw [point]
  rfl

include first rest in
theorem input (i : Fin I.length) : (occurrence hi B R f r apart).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by rw [hi];simp⟩ := Fin.ext zero
    subst i
    exact (BareApplyFirst.Join.input_zero (family B R) (head B f) (familyOccurrence B R f r apart) (head_function B R f r apart) (head_family B R f r apart)).trans (head_input hi B f first)
  · let j : Fin n := ⟨i.val-1,by have h:=i.isLt; have len := congrArg List.length hi; simp only [List.length_replicate] at len;omega⟩
    have eq : (Fin.cast (congrArg List.length hi) i) = ⟨j.val+1,by simp⟩ := Fin.ext (by dsimp[j];omega)
    change (BareApplyFirst.Join.occurrence (family B R) (head B f) (familyOccurrence B R f r apart) (head_function B R f r apart) (head_family B R f r apart)).ports (.input (Fin.cast (congrArg List.length hi) i)) = _
    rw [eq,BareApplyFirst.Join.input_succ,family_succ hi B R f r apart rest]
    exact congrArg Port.input (Fin.ext (by dsimp[j];omega))

include out in
theorem output (i : Fin ([Wire.term].length)) : (occurrence hi B R f r apart).ports (.output i) = .output i := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  exact (BareApplyFirst.Join.output (family B R) (head B f) (familyOccurrence B R f r apart) (head_function B R f r apart) (head_family B R f r apart)).trans (head_argument B f out)

variable (cover : ∀ e : G.Edge, (∃ a, f.edges a=e) ∨ ∃ b, r.edges b=e)
include cover in
theorem covers : Function.Surjective (occurrence hi B R f r apart).edges := by
  intro e
  cases e with
  | inl e =>
    obtain ⟨e,ne⟩ := e
    cases e with
    | none => exact False.elim (ne rfl)
    | some e =>
      rcases cover e.val with ⟨x,eq⟩ | ⟨x,eq⟩
      · exact False.elim (e.property x eq)
      · refine ⟨⟨true,⟨true,x⟩⟩,?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        exact Subtype.ext eq
  | inr e =>
    cases e
    · exact ⟨⟨false,(0 : Fin 1)⟩,rfl⟩
    · exact ⟨⟨true,⟨false,⟨false,(0 : Fin 1)⟩⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩,rfl⟩

/-- Exact source correspondence for the inverse opening, exposing the
original argument as the sole output rather than retaining its graph. -/
noncomputable def iso : DeepIso ((BareApplyFirst.net (family B R)).reboundary hi.symm rfl) (target B f) :=
  (occurrence hi B R f r apart).iso_of_edge_surjective
    (input hi B R f r apart first rest) (output hi B R f r apart out)
    (covers hi B R f r apart cover)

end Hypernets.Copying.Parametricity.RightBareApplicationCut

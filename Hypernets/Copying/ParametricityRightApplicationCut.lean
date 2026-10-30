import Hypernets.Copying.ParametricityApplyJoin
import Hypernets.Copying.ParametricityApplyOccurrence
import Hypernets.Copying.OccurrenceCutBoundary
import Hypernets.Copying.ParametricityPointedCut

/-! A closed selected abstraction and its complete untouched family are
reconstructed from an actual local beta-source replacement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.RightApplicationCut
open Graph Opening
variable {d n I O} (hi : I = List.replicate (n+1) Wire.term)
    {A : Hypernet (d+2) [.term] O} {G : Hypernet (d+2) I O}
    (R : Hypernet (d+2) (List.replicate n .term) []) (L : Hypernet (d+2) [.term] []) (V : Hypernet (d+2) [.term] O)
    (f : Occurrence A G) (r : Occurrence R G)
    (apart : ∀ e a, f.edges e ≠ r.edges a)

abbrev localSource := Serial.net (primitiveNet (d+2) (.operation .app)) (Net.Tensor.net L V)
noncomputable abbrev target := CompleteMatchCut.replaceWith f.matchEmbedding f.label (localSource L V)
noncomputable def inserted : Occurrence (localSource L V) (target L V f) := f.replacement (localSource L V)
noncomputable def head := (BoxPullWeakening.ReverseComponents.serialLeft
  (primitiveNet (d+2) (.operation .app)) (Net.Tensor.net L V)).comp (inserted L V f)
noncomputable def arguments := (BoxPullWeakening.ReverseComponents.serialRight
  (primitiveNet (d+2) (.operation .app)) (Net.Tensor.net L V)).comp (inserted L V f)
noncomputable def selected := (BoxPullWeakening.ReverseComponents.tensorLeft L V).comp (arguments L V f)
noncomputable def argument := (BoxPullWeakening.ReverseComponents.tensorRight L V).comp (arguments L V f)
noncomputable def remaining := f.acrossCut r apart (localSource L V)

def family : Hypernet (d+2) (List.replicate (n+1) .term) [] :=
  (Net.Tensor.net L R).reboundary (by simp [List.replicate_succ]) rfl

theorem selected_remaining : ∀ e a, (selected L V f).edges e ≠ (remaining R L V f r apart).edges a := by
  intro e a eq; cases eq
noncomputable def familyOccurrence : Occurrence (family R L) (target L V f) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected L V f) (remaining R L V f r apart)
    (selected_remaining R L V f r apart)).reboundarySource _ _

theorem family_zero : (familyOccurrence R L V f r apart).ports (.input ⟨0,by simp⟩) =
    (selected L V f).ports (.input (0 : Fin 1)) := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected L V f) (remaining R L V f r apart) (selected_remaining R L V f r apart)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft L R).ports (.input (0 : Fin 1))) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem head_function : (head L V f).ports (.output (0 : Fin 2)) =
    (familyOccurrence R L V f r apart).ports (.input ⟨0,by simp⟩) := by rw [family_zero]; rfl
theorem head_argument : (head L V f).ports (.output (1 : Fin 2)) =
    (argument L V f).ports (.input (0 : Fin 1)) := rfl

theorem head_family : ∀ e a, (head L V f).edges e ≠ (familyOccurrence R L V f r apart).edges a := by
  rintro e ⟨part,a⟩ eq; cases part <;> cases eq
theorem head_arg : ∀ e a, (head L V f).edges e ≠ (argument L V f).edges a := by
  intro e a eq; cases eq
theorem family_arg : ∀ e a, (familyOccurrence R L V f r apart).edges e ≠ (argument L V f).edges a := by
  rintro ⟨part,e⟩ a eq; cases part <;> cases eq

noncomputable def occurrence : Occurrence ((ApplyFirst.net (family R L) V).reboundary hi.symm rfl) (target L V f) :=
  (ApplyFirst.Join.occurrence (family R L) V (head L V f) (familyOccurrence R L V f r apart)
    (argument L V f) (head_function R L V f r apart) (head_argument L V f)
    (head_family R L V f r apart) (head_arg L V f) (family_arg R L V f r apart)).reboundarySource hi.symm rfl

variable (first : f.ports (.input (0 : Fin 1)) = .input ⟨0,by rw [hi];simp⟩)
    (rest : ∀ i : Fin n, r.ports (.input ⟨i.val,by simp⟩) = .input ⟨i.val+1,by rw [hi];simp⟩)
    (out : ∀ i : Fin O.length, f.ports (.output i) = .output i)

include first in
theorem head_input : (head L V f).ports (.input (0 : Fin 1)) = .input ⟨0,by rw [hi];simp⟩ := by
  change CompleteMatchCut.replacePort f.matchEmbedding f.label (localSource L V) (.input (0 : Fin 1)) = _
  exact CompleteMatchCut.replace_input _ _ _ _ first

include rest in
theorem family_succ (i : Fin n) : (familyOccurrence R L V f r apart).ports (.input ⟨i.val+1,by simp⟩) =
    .input ⟨i.val+1,by rw [hi];simp⟩ := by
  have eq := Occurrence.tensorJoin_right (selected L V f) (remaining R L V f r apart)
    (selected_remaining R L V f r apart) (.input ⟨i.val,by simp⟩)
  have represented : (BoxPullWeakening.ReverseComponents.tensorRight L R).ports (.input ⟨i.val,by simp⟩) =
      .input ⟨i.val+1,by simp⟩ := by
    exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1;omega))
  rw [represented] at eq
  exact eq.trans (f.acrossCut_input r apart (localSource L V) (rest i))

include out in
theorem argument_output (i : Fin O.length) : (argument L V f).ports (.output i) = .output i := by
  change (inserted L V f).ports (BoundarySerial.rightInsert (primitiveNet (d+2) (.operation .app))
    (Net.Tensor.net L V) ((BoxPullWeakening.ReverseComponents.tensorRight L V).ports (.output i))) = _
  have point : (BoxPullWeakening.ReverseComponents.tensorRight L V).ports (.output i) = .output i := by
    exact congrArg Port.output (Fin.ext (by change 0+i.val=i.val;simp))
  rw [point,Application.right_serial_output]
  change CompleteMatchCut.replacePort f.matchEmbedding f.label (localSource L V) (.output i) = _
  change Net.Replacement.host (CompleteMatchCut.net f.matchEmbedding f.label) none _
    ((CompleteMatchCut.net f.matchEmbedding f.label).targetPort none (Fin.cast (congrArg List.length (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm) i)) = _
  rw [CompleteMatchCut.hole_targetPort]
  have point : CompleteMatchCut.outputPort f.matchEmbedding i = .output i :=
    CompleteMatchCut.embed_injective f.matchEmbedding ((CompleteMatchCut.embed_output f.matchEmbedding i).trans (out i))
  rw [point]
  rfl

include first rest in
theorem input (i : Fin I.length) : (occurrence hi R L V f r apart).ports (.input i) = .input i := by
  by_cases zero : i.val=0
  · have eq : i=⟨0,by rw [hi];simp⟩ := Fin.ext zero
    subst i
    exact (ApplyFirst.Join.input_zero (family R L) V (head L V f) (familyOccurrence R L V f r apart) (argument L V f) (head_function R L V f r apart) (head_argument L V f) (head_family R L V f r apart) (head_arg L V f) (family_arg R L V f r apart)).trans (head_input hi L V f first)
  · let j : Fin n := ⟨i.val-1,by have h:=i.isLt; have len := congrArg List.length hi; simp only [List.length_replicate] at len;omega⟩
    have eq : (Fin.cast (congrArg List.length hi) i) = ⟨j.val+1,by simp⟩ := Fin.ext (by dsimp[j];omega)
    change (ApplyFirst.Join.occurrence (family R L) V (head L V f) (familyOccurrence R L V f r apart) (argument L V f) (head_function R L V f r apart) (head_argument L V f) (head_family R L V f r apart) (head_arg L V f) (family_arg R L V f r apart)).ports (.input (Fin.cast (congrArg List.length hi) i)) = _
    rw [eq,ApplyFirst.Join.input_succ,family_succ hi R L V f r apart rest]
    exact congrArg Port.input (Fin.ext (by dsimp[j];omega))

include out in
theorem output (i : Fin O.length) : (occurrence hi R L V f r apart).ports (.output i) = .output i :=
  (ApplyFirst.Join.output (family R L) V (head L V f) (familyOccurrence R L V f r apart) (argument L V f) (head_function R L V f r apart) (head_argument L V f) (head_family R L V f r apart) (head_arg L V f) (family_arg R L V f r apart) i).trans (argument_output L V f out i)

variable (cover : ∀ e : G.Edge, (∃ a, f.edges a=e) ∨ ∃ b, r.edges b=e)
include cover in
theorem covers : Function.Surjective (occurrence hi R L V f r apart).edges := by
  intro e
  cases e with
  | inl e =>
    obtain ⟨e,ne⟩ := e
    cases e with
    | none => exact False.elim (ne rfl)
    | some e =>
      rcases cover e.val with ⟨x,eq⟩ | ⟨x,eq⟩
      · exact False.elim (e.property x eq)
      · refine ⟨⟨some false,⟨true,x⟩⟩,?_⟩
        apply congrArg Sum.inl
        apply Subtype.ext
        apply congrArg Option.some
        exact Subtype.ext eq
  | inr e =>
    obtain ⟨part,e⟩ := e
    cases part
    · exact ⟨⟨none,e⟩,rfl⟩
    · obtain ⟨part,e⟩ := e
      cases part
      · exact ⟨⟨some false,⟨false,e⟩⟩,rfl⟩
      · exact ⟨⟨some true,e⟩,rfl⟩

/-- The actual computed predecessor is exactly the ordinary application to
its original closed lambda and untouched family, not a conditional residual. -/
noncomputable def iso : DeepIso ((ApplyFirst.net (family R L) V).reboundary hi.symm rfl) (target L V f) :=
  (occurrence hi R L V f r apart).iso_of_edge_surjective
    (input hi R L V f r apart first rest) (output hi R L V f r apart out)
    (covers hi R L V f r apart cover)

end Hypernets.Copying.Parametricity.RightApplicationCut

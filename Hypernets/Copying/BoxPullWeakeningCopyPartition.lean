import Hypernets.Copying.BoxPullWeakeningCopyInjection
import Hypernets.Copying.OccurrenceAcrossCut
import Hypernets.Copying.OccurrenceCoverIso

/-! The unchanged copy reduct and the selected unused row partition all
original edge occurrences of the extended reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.RetainedCopy
open Graph Opening
variable {d n k h} (T : ContractionTree .term (n+1))
  (H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

theorem row_disjoint : ∀ a b, (CopyRow.occurrence T H s).edges a ≠ (after T H s).edges b := by
  cases d <;> cases s
  all_goals
    rintro ⟨a,e⟩ ⟨b,c⟩ eq
    cases a <;> cases b
    · rcases e with ⟨u,e⟩; rcases c with ⟨v,c⟩
      cases u <;> cases v
      all_goals first
        | cases eq
        | (rcases c with ⟨w,c⟩; cases w <;> cases eq)
    · rcases e with ⟨u,e⟩; cases u <;> cases eq
    · cases eq
    · rcases c with ⟨v,c⟩
      cases v
      all_goals rcases c with ⟨i,c⟩
      all_goals first
        | cases eq
        | (have middle := eq_of_heq (Sigma.mk.inj eq).2
           have inner := eq_of_heq (Sigma.mk.inj middle).2
           have resources := congrArg Sigma.fst inner
           have values := congrArg Fin.val resources
           have bound := i.isLt
           simp only [termResource] at values
           omega)

/-- Every edge of the actual extended reduct belongs to exactly the old
copy construction or the selected five-edge weakening row. -/
theorem edge_cover (e : (CopyRule.after T (extend H s)).Edge) :
    (∃ a, (CopyRow.occurrence T H s).edges a = e) ∨
      ∃ b, (after T H s).edges b = e := by
  cases d <;> cases s
  all_goals
    rcases e with ⟨a,e⟩
    cases a
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨c,e⟩
        cases c
        · exact .inr ⟨⟨false,⟨false,e⟩⟩,rfl⟩
        · have zero : e = (0 : Fin 1) := Fin.ext (by have := e.isLt; omega)
          subst e
          exact .inl ⟨⟨false,⟨false,(0 : Fin 1)⟩⟩,rfl⟩
      · rcases e with ⟨c,e⟩
        cases c
        · exact .inr ⟨⟨false,⟨true,⟨false,e⟩⟩⟩,rfl⟩
        · rcases e with ⟨c,e⟩
          cases c
          · exact .inr ⟨⟨false,⟨true,⟨true,e⟩⟩⟩,rfl⟩
          · have zero : e = (0 : Fin 1) := Fin.ext (by have := e.isLt; omega)
            subst e
            exact .inl ⟨⟨false,⟨true,(0 : Fin 1)⟩⟩,rfl⟩
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨i,e⟩
        first
        | exact .inr ⟨⟨true,⟨false,⟨i,e⟩⟩⟩,rfl⟩
        | (by_cases last : i.val = k
           · have eq : i = ⟨k,by change k < k+1; omega⟩ := Fin.ext last
             refine .inl ⟨⟨true,e⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk false)
             exact congrArg (fun j : Fin (k+1) => (⟨j,e⟩ : Σ _ : Fin (k+1), Fin 3)) eq.symm
           · let j : Fin k := ⟨i.val,by have bound := i.isLt; change i.val < k+1 at bound; omega⟩
             have eq : i = termResource .term j := Fin.ext rfl
             refine .inr ⟨⟨true,⟨false,⟨j,e⟩⟩⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk false)
             exact congrArg (fun j : Fin (k+1) => (⟨j,e⟩ : Σ _ : Fin (k+1), Fin 3)) eq.symm)
      · rcases e with ⟨i,e⟩
        first
        | exact .inr ⟨⟨true,⟨true,⟨i,e⟩⟩⟩,rfl⟩
        | (by_cases zero : i.val = 0
           · have eq : i = ⟨0,by change 0 < h+1; omega⟩ := Fin.ext zero
             refine .inl ⟨⟨true,e⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk true)
             exact congrArg (fun j : Fin (h+1) => (⟨j,e⟩ : Σ _ : Fin (h+1), Fin 3)) eq.symm
           · let j : Fin h := ⟨i.val-1,by have bound := i.isLt; change i.val < h+1 at bound; omega⟩
             have eq : i = atomResource .atom j := Fin.ext (by change i.val = (i.val-1)+1; omega)
             refine .inr ⟨⟨true,⟨true,⟨j,e⟩⟩⟩,?_⟩
             apply congrArg (Sigma.mk true)
             apply congrArg (Sigma.mk true)
             exact congrArg (fun j : Fin (h+1) => (⟨j,e⟩ : Σ _ : Fin (h+1), Fin 3)) eq.symm)

/-- The complete old reduct survives both Idem contractions through the
computed complement of the selected row. -/
noncomputable def retained : Occurrence (CopyRule.after T H) (CopyRow.corrected T H s) :=
  (CopyRow.occurrence T H s).acrossCut (after T H s) (row_disjoint T H s)
    (primitiveNet d (.weakening s))

/-- The sole added weakening is the actual inserted component of the final
computed replacement, with the original ordered output attachment. -/
noncomputable def inserted : Occurrence (primitiveNet d (.weakening s)) (CopyRow.corrected T H s) :=
  by
  unfold CopyRow.corrected CompleteMatchCut.replaceWith
  exact (targetCast (Occurrence.ofIso (DeepIso.refl (primitiveNet d (.weakening s))))
    (CompleteMatchCut.hole_input (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label).symm
    (CompleteMatchCut.hole_output (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label).symm).comp
      (Occurrence.plug (CompleteMatchCut.net (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label) none _)

noncomputable def finalComponents (b : Bool) :
    Occurrence (Net.Tensor.family (CopyRule.after T H) (primitiveNet d (.weakening s)) b)
      (CopyRow.corrected T H s) :=
  match b with
  | false => retained T H s
  | true => inserted T H s

theorem finalComponents_disjoint :
    ∀ a b, a ≠ b → ∀ e c, (finalComponents T H s a).edges e ≠ (finalComponents T H s b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · cases eq
  · cases eq
  · exact ne rfl

/-- The intended outside-weakening reduct has an actual complete occurrence
in the twice-corrected graph. Edge coverage below will upgrade it to an iso. -/
noncomputable def normalizationOccurrence :
    Occurrence (extend (CopyRule.after T H) s) (CopyRow.corrected T H s) :=
  (Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (CopyRule.after T H) (primitiveNet d (.weakening s)))
    (insertionBoundary (List.replicate (n+1) .term) (List.replicate k .term) (List.replicate h .atom) s)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (finalComponents T H s)
    (finalComponents_disjoint T H s)).reboundarySource (List.append_nil _) (extended_interface s k h)

theorem normalization_old_port (v : (CopyRule.after T H).Vertex) :
    (normalizationOccurrence T H s).ports ((payload (CopyRule.after T H) s).ports v) =
      (retained T H s).ports v := by
  unfold normalizationOccurrence payload
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]
  rfl

theorem retained_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (retained T H s).ports (.input i) = .input i := by
  have cut : Occurrence.cutPort (CopyRow.occurrence T H s) (after T H s)
      (row_disjoint T H s) (.input i) = .input i := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans (after_input T H s i)
  change Net.Replacement.host
    (CompleteMatchCut.net (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label)
    none ((primitiveNet d (.weakening s)).reboundary _ _)
    (Occurrence.cutPort (CopyRow.occurrence T H s) (after T H s) (row_disjoint T H s) (.input i)) = _
  rw [cut]
  rfl

theorem retained_output (i : Fin (environmentInterface k h).length) :
    (retained T H s).ports (.output i) = .output (outputIndex s i) := by
  have cut : Occurrence.cutPort (CopyRow.occurrence T H s) (after T H s)
      (row_disjoint T H s) (.output i) = .output (outputIndex s i) := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans (after_output T H s i)
  change Net.Replacement.host
    (CompleteMatchCut.net (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label)
    none ((primitiveNet d (.weakening s)).reboundary _ _)
    (Occurrence.cutPort (CopyRow.occurrence T H s) (after T H s) (row_disjoint T H s) (.output i)) = _
  rw [cut]
  rfl

theorem original_row_output (i : Fin 1) :
    (CopyRow.occurrence T H s).ports (.output i) = .output (CopyRow.addedOutput k h s) := by
  have zero : i = 0 := Fin.ext (by omega)
  subst i
  cases d
  all_goals
    change (CopyRow.row T H s).ports (.output 0) = _
    simp only [CopyRow.row,Occurrence.comp,Occurrence.serialRight,Function.comp_apply]
    cases s <;> simp only [CopyRow.selected,CopyRow.termOccurrence,CopyRow.atomOccurrence,CopyRow.forestOccurrence,Net.Parallel.embed]
    all_goals
      rw [Application.right_serial_output]
      apply congrArg Port.output
      apply Fin.ext
      simp [CopyRow.addedOutput,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,List.length_replicate]

theorem inserted_output (i : Fin 1) :
    (inserted T H s).ports (.output i) = .output (CopyRow.addedOutput k h s) := by
  change Net.Replacement.host _ none _
    ((CompleteMatchCut.net (CopyRow.occurrence T H s).matchEmbedding (CopyRow.occurrence T H s).label).targetPort none
      (Fin.cast (congrArg List.length
        (CompleteMatchCut.hole_output (CopyRow.occurrence T H s).matchEmbedding
          (CopyRow.occurrence T H s).label).symm) i)) = _
  rw [CompleteMatchCut.hole_targetPort]
  have cut : CompleteMatchCut.outputPort (CopyRow.occurrence T H s).matchEmbedding i =
      .output (CopyRow.addedOutput k h s) := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_output (CopyRow.occurrence T H s).matchEmbedding i).trans (original_row_output T H s i)
  rw [cut]
  rfl


theorem normalization_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (normalizationOccurrence T H s).ports (.input i) = .input i := by
  rw [← payload_input (CopyRule.after T H) s i,normalization_old_port,retained_input]

theorem normalization_component_output (b : Bool)
    (i : Fin (Net.Tensor.interfaces (environmentInterface k h) [s.wire] b).length) :
    (finalComponents T H s b).ports (.output i) =
      .output (Fin.cast (congrArg List.length (extended_interface s k h))
        ((insertionBoundary (List.replicate (n+1) .term) (List.replicate k .term)
          (List.replicate h .atom) s).outputs.toFun ⟨b,i⟩)) := by
  cases b
  · change (retained T H s).ports (.output i) = _
    rw [retained_output]
    apply congrArg Port.output
    apply Fin.ext
    exact (inserted_old_output (I := List.replicate (n+1) .term) s i).symm
  · change (inserted T H s).ports (.output i) = _
    rw [inserted_output]
    have zero : i = (0 : Fin 1) := Fin.ext (by have bound := i.isLt; change i.val < 1 at bound; change i.val = 0; omega)
    subst i
    apply congrArg Port.output
    apply Fin.ext
    change k = _
    simpa only [Fin.val_cast,List.length_replicate] using
      (inserted_weakening_output (I := List.replicate (n+1) .term)
        (A := List.replicate k .term) (B := List.replicate h .atom) s).symm

/-- The reconstruction has the original ordered external interface. -/
theorem normalization_output (i : Fin (environmentInterface (variables s k) (atoms s h)).length) :
    (normalizationOccurrence T H s).ports (.output i) = .output i := by
  let B := insertionBoundary (List.replicate (n+1) .term) (List.replicate k .term) (List.replicate h .atom) s
  let j := Fin.cast (congrArg List.length (extended_interface s k h).symm) i
  have eq := B.outputs.right_inv j
  change (finalComponents T H s (B.outputs.invFun j).1).ports (.output (B.outputs.invFun j).2) = _
  rw [normalization_component_output]
  change Port.output (Fin.cast _ (B.outputs.toFun (B.outputs.invFun j))) = _
  rw [eq]
  rfl

/-- No edge remains hidden in the computed complement: the selected row and
unchanged original reduct were an exhaustive partition. -/
theorem normalization_edge_surjective : Function.Surjective (normalizationOccurrence T H s).edges := by
  cases d
  all_goals
    intro e
    cases e with
    | inl e =>
      rcases e with ⟨e,ne⟩
      cases e with
      | none => exact False.elim (ne rfl)
      | some e =>
        rcases edge_cover T H s e.val with row | old
        · obtain ⟨a,eq⟩ := row
          exact False.elim (e.property a eq)
        · obtain ⟨b,eq⟩ := old
          refine ⟨⟨false,b⟩,?_⟩
          apply congrArg Sum.inl
          apply Subtype.ext
          apply congrArg Option.some
          exact Subtype.ext eq
    | inr e => exact ⟨⟨true,e⟩,rfl⟩

/-- The literal original copying reduct, after its two proved Idem corrections,
is exactly the outside-weakening reduct up to recursive graph representation. -/
noncomputable def normalizationIso :
    DeepIso (extend (CopyRule.after T H) s) (CopyRow.corrected T H s) :=
  (normalizationOccurrence T H s).iso_of_edge_surjective
    (normalization_input T H s) (normalization_output T H s) (normalization_edge_surjective T H s)

end Hypernets.Copying.BoxPullWeakening.RetainedCopy

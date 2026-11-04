import Hypernets.Copying.BoxPullWeakeningCopyPartition
import Hypernets.Copying.WeakeningCalculation

/-! Exact correction of a complete unused binary row in an arbitrary host.
The edge partition and ordered port laws are explicit geometric data. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.RowPartition
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (outputIndex payload payload_input targetCast)

/-- A whole graph consists of the unchanged old graph and the exact canonical
binary row fed by two weakenings. All external attachments are recorded. -/
structure Partition {d I k h} (s : ShareSort)
    (G : Hypernet d I (environmentInterface k h))
    (H : Hypernet d I (environmentInterface (variables s k) (atoms s h))) where
  row : Occurrence (IdemRow.canonical d s) H
  old : Occurrence G H
  disjoint : ∀ a b, row.edges a ≠ old.edges b
  cover : ∀ e, (∃ a, row.edges a = e) ∨ ∃ b, old.edges b = e
  input : ∀ i, old.ports (.input i) = .input i
  output : ∀ i, old.ports (.output i) = .output (outputIndex s i)
  row_output : ∀ i, row.ports (.output i) = .output (CopyRow.addedOutput k h s)

variable {d I k h s} {G : Hypernet d I (environmentInterface k h)}
    {H : Hypernet d I (environmentInterface (variables s k) (atoms s h))}
    (q : Partition s G H)

/-- The actual finite complement with the selected row replaced by one weakening. -/
noncomputable def corrected :=
  CompleteMatchCut.replaceWith q.row.matchEmbedding q.row.label (primitiveNet d (.weakening s))

/-- The complete old reduct survives both Idem contractions through the
computed complement of the selected row. -/
noncomputable def retained : Occurrence (G) (corrected q) :=
  (q.row).acrossCut (q.old) (q.disjoint)
    (primitiveNet d (.weakening s))

/-- The sole added weakening is the actual inserted component of the final
computed replacement, with the original ordered output attachment. -/
noncomputable def inserted : Occurrence (primitiveNet d (.weakening s)) (corrected q) :=
  by
  unfold corrected CompleteMatchCut.replaceWith
  exact (targetCast (Occurrence.ofIso (DeepIso.refl (primitiveNet d (.weakening s))))
    (CompleteMatchCut.hole_input (q.row).matchEmbedding (q.row).label).symm
    (CompleteMatchCut.hole_output (q.row).matchEmbedding (q.row).label).symm).comp
      (Occurrence.plug (CompleteMatchCut.net (q.row).matchEmbedding (q.row).label) none _)

noncomputable def finalComponents (b : Bool) :
    Occurrence (Net.Tensor.family (G) (primitiveNet d (.weakening s)) b)
      (corrected q) :=
  match b with
  | false => retained q
  | true => inserted q

theorem finalComponents_disjoint :
    ∀ a b, a ≠ b → ∀ e c, (finalComponents q a).edges e ≠ (finalComponents q b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · cases eq
  · cases eq
  · exact ne rfl

/-- The intended outside-weakening reduct has an actual complete occurrence
in the twice-corrected graph. Edge coverage below will upgrade it to an iso. -/
noncomputable def normalizationOccurrence :
    Occurrence (extend (G) s) (corrected q) :=
  (Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family (G) (primitiveNet d (.weakening s)))
    (insertionBoundary (I) (List.replicate k .term) (List.replicate h .atom) s)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (finalComponents q)
    (finalComponents_disjoint q)).reboundarySource (List.append_nil _) (extended_interface s k h)

theorem normalization_old_port (v : (G).Vertex) :
    (normalizationOccurrence q).ports ((payload (G) s).ports v) =
      (retained q).ports v := by
  unfold normalizationOccurrence payload
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]
  rfl

theorem retained_input (i : Fin (I).length) :
    (retained q).ports (.input i) = .input i := by
  have cut : Occurrence.cutPort (q.row) (q.old)
      (q.disjoint) (.input i) = .input i := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans (q.input i)
  change Net.Replacement.host
    (CompleteMatchCut.net (q.row).matchEmbedding (q.row).label)
    none ((primitiveNet d (.weakening s)).reboundary _ _)
    (Occurrence.cutPort (q.row) (q.old) (q.disjoint) (.input i)) = _
  rw [cut]
  rfl

theorem retained_output (i : Fin (environmentInterface k h).length) :
    (retained q).ports (.output i) = .output (outputIndex s i) := by
  have cut : Occurrence.cutPort (q.row) (q.old)
      (q.disjoint) (.output i) = .output (outputIndex s i) := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_project _ _ _).trans (q.output i)
  change Net.Replacement.host
    (CompleteMatchCut.net (q.row).matchEmbedding (q.row).label)
    none ((primitiveNet d (.weakening s)).reboundary _ _)
    (Occurrence.cutPort (q.row) (q.old) (q.disjoint) (.output i)) = _
  rw [cut]
  rfl

theorem inserted_output (i : Fin 1) :
    (inserted q).ports (.output i) = .output (CopyRow.addedOutput k h s) := by
  change Net.Replacement.host _ none _
    ((CompleteMatchCut.net (q.row).matchEmbedding (q.row).label).targetPort none
      (Fin.cast (congrArg List.length
        (CompleteMatchCut.hole_output (q.row).matchEmbedding
          (q.row).label).symm) i)) = _
  rw [CompleteMatchCut.hole_targetPort]
  have cut : CompleteMatchCut.outputPort (q.row).matchEmbedding i =
      .output (CopyRow.addedOutput k h s) := by
    apply CompleteMatchCut.embed_injective
    exact (CompleteMatchCut.embed_output (q.row).matchEmbedding i).trans (q.row_output i)
  rw [cut]
  rfl


theorem normalization_input (i : Fin (I).length) :
    (normalizationOccurrence q).ports (.input i) = .input i := by
  rw [← payload_input (G) s i,normalization_old_port,retained_input]

theorem normalization_component_output (b : Bool)
    (i : Fin (Net.Tensor.interfaces (environmentInterface k h) [s.wire] b).length) :
    (finalComponents q b).ports (.output i) =
      .output (Fin.cast (congrArg List.length (extended_interface s k h))
        ((insertionBoundary (I) (List.replicate k .term)
          (List.replicate h .atom) s).outputs.toFun ⟨b,i⟩)) := by
  cases b
  · change (retained q).ports (.output i) = _
    rw [retained_output]
    apply congrArg Port.output
    apply Fin.ext
    exact (inserted_old_output (I := I) s i).symm
  · change (inserted q).ports (.output i) = _
    rw [inserted_output]
    have zero : i = (0 : Fin 1) := Fin.ext (by have bound := i.isLt; change i.val < 1 at bound; change i.val = 0; omega)
    subst i
    apply congrArg Port.output
    apply Fin.ext
    change k = _
    simpa only [Fin.val_cast,List.length_replicate] using
      (inserted_weakening_output (I := I)
        (A := List.replicate k .term) (B := List.replicate h .atom) s).symm

/-- The reconstruction has the original ordered external interface. -/
theorem normalization_output (i : Fin (environmentInterface (variables s k) (atoms s h)).length) :
    (normalizationOccurrence q).ports (.output i) = .output i := by
  let B := insertionBoundary (I) (List.replicate k .term) (List.replicate h .atom) s
  let j := Fin.cast (congrArg List.length (extended_interface s k h).symm) i
  have eq := B.outputs.right_inv j
  change (finalComponents q (B.outputs.invFun j).1).ports (.output (B.outputs.invFun j).2) = _
  rw [normalization_component_output]
  change Port.output (Fin.cast _ (B.outputs.toFun (B.outputs.invFun j))) = _
  rw [eq]
  rfl

/-- No edge remains hidden in the computed complement: the selected row and
unchanged original reduct were an exhaustive partition. -/
theorem normalization_edge_surjective : Function.Surjective (normalizationOccurrence q).edges := by
  cases d
  all_goals
    intro e
    cases e with
    | inl e =>
      rcases e with ⟨e,ne⟩
      cases e with
      | none => exact False.elim (ne rfl)
      | some e =>
        rcases q.cover e.val with row | old
        · obtain ⟨a,eq⟩ := row
          exact False.elim (e.property a eq)
        · obtain ⟨b,eq⟩ := old
          refine ⟨⟨false,b⟩,?_⟩
          apply congrArg Sum.inl
          apply Subtype.ext
          apply congrArg Option.some
          exact Subtype.ext eq
    | inr e => exact ⟨⟨true,e⟩,rfl⟩

/-- The whole graph, after its two proved Idem corrections,
is exactly the old graph with one outside weakening up to recursive graph representation. -/
noncomputable def normalizationIso :
    DeepIso (extend (G) s) (corrected q) :=
  (normalizationOccurrence q).iso_of_edge_surjective
    (normalization_input q) (normalization_output q) (normalization_edge_surjective q)

/-- Two genuine Idem fillings correct the entire partitioned host. The
conclusion contains no assumed execution equivalence. -/
noncomputable def normalize (free : FocusFree H) : Calculation H (extend G s) :=
  (Calculation.idem (IdemRow.cut_first q.row free)).trans
    (.idem ((IdemRow.cut_second q.row free).congr (DeepIso.refl _) (normalizationIso q).symm))

end Hypernets.Copying.Weakening.RowPartition

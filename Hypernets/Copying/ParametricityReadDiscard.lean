import Hypernets.Copying.ParametricityReadResidual
import Hypernets.Copying.BoxPullContractionCutLinks

/-! The discarded reference instance left by the actual read rule is a
literal garbage-collection instance. Its complete match is disjoint from
the full stored-content copying occurrence, so it survives both corrections. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail.Discard
open Graph Opening
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

def weak (d : Nat) : LabelCopy ((ContractionTree.canonical .term 0).atDepth d)
    (primitiveLabel d (.weakening .term)) :=
  by cases d <;> exact ⟨(0 : Fin 1),rfl,rfl,rfl,fun x => Fin.ext (by change x.val = 0; have bound := x.isLt; change x.val < 1 at bound; omega)⟩

noncomputable def weakOccurrence :
    Occurrence ((ContractionTree.canonical .term 0).atDepth d) (afterRead T d) :=
  (Occurrence.ofIso ((weak d).iso (Occurrence.primitiveCopy d (.weakening .term))
    (labelEquiv_refl _ _))).comp
      (Occurrence.primitive (afterRead T d)
        (Serial.leftEdge _ _ ⟨.discard,(0 : Fin 1)⟩) (by cases d <;> rfl))

noncomputable def instanceOccurrence : Occurrence (primitiveNet d .instanceEdge) (afterRead T d) :=
  Occurrence.primitive (afterRead T d) (Serial.leftEdge _ _ ⟨.inst,(0 : Fin 1)⟩) (by cases d <;> rfl)

theorem boundary (i : Fin [Wire.term].length) :
    (weakOccurrence T d).ports (.output i) = (instanceOccurrence T d).ports (.input i) := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  cases d <;> rfl

theorem disjoint : ∀ e c, (weakOccurrence T d).edges e ≠ (instanceOccurrence T d).edges c := by
  cases d <;> intro e c eq
  all_goals
    have eq := eq_of_heq (Sigma.mk.inj eq).2
    have impossible := congrArg Sigma.fst eq
    cases impossible

/-- The actual term weakening and the consumed reference instance together
form the complete zero-input GC source, preserving its exposed atom wire. -/
noncomputable def occurrence :
    Occurrence (GarbageCollection.left (k := 0) (h := 1) (ContractionTree.canonical .term 0)
      (primitiveNet d .instanceEdge)) (afterRead T d) :=
  Occurrence.SerialJoin.occurrence (weakOccurrence T d) (instanceOccurrence T d)
    (boundary T d) (disjoint T d)

/-- Stored-content copying and reference-instance collection have disjoint
original edges, even though their surrounding store connects their outputs. -/
theorem content_disjoint : ∀ a b,
    (FullCopy.occurrence T d).edges a ≠ (occurrence T d).edges b := by
  cases d
  all_goals
    rintro ⟨a,e⟩ ⟨b,c⟩ eq
    cases a <;> cases b
    all_goals
      first
      | cases eq
      | (have inner := eq_of_heq (Sigma.mk.inj eq).2
         have impossible := congrArg Sigma.fst inner
         cases impossible)

/-- The GC occurrence is retained in the actual corrected stored-content
graph by the proved complement transport, without a locality assumption. -/
noncomputable def retained :
    Occurrence (GarbageCollection.left (k := 0) (h := 1) (ContractionTree.canonical .term 0)
      (primitiveNet d .instanceEdge)) (FullCopy.separated T d) :=
  (FullCopy.occurrence T d).acrossCut (occurrence T d) (content_disjoint T d)
    (ClosedCopyPair.selectedPair (numeral d) 1)

noncomputable def collected : Hypernet d (Dereference.inputs h) [] :=
  CompleteMatchCut.replaceWith (retained T d).matchEmbedding (retained T d).label
    (GarbageCollection.right d 0 1)

/-- Collect exactly the consumed instance; the actual store and its constant
content remain present in the retained complement. -/
noncomputable def witness : FillingWitness GarbageCollection.template
    (FullCopy.separated T d) (collected T d) :=
  CompleteMatchCut.filling (retained T d).matchEmbedding (retained T d).label
    (FullCopy.garbageResidual T d).filling.focusFree.2
    (FillingWitness.of_rel 0 (GarbageCollection.literal (k := 0) (h := 1) (ContractionTree.canonical .term 0)
      (primitiveNet d .instanceEdge) (.instanceEdge d) (by cases d <;> intro e m eq <;> cases eq)))

/-- The consumed-instance collection preserves the actual active reader
position, proved to be the original read-result input by the cut attachment. -/
noncomputable def pointed : BoxPullWeakening.PointedWitness GarbageCollection.template
    (FullCopy.separated T d) (FullCopy.separatedPoint T d)
    (collected T d) (.input ⟨0,by simp [Dereference.inputs]⟩) := by
  rw [FullCopy.separatedPoint_input]
  exact BoxPullWeakening.PointedWitness.input (witness T d) ⟨0,by simp [Dereference.inputs]⟩

end Hypernets.Copying.Parametricity.ReadTail.Discard

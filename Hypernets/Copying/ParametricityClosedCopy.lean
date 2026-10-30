import Hypernets.Copying.CopyingDoubleInterchange
import Hypernets.Copying.GarbageCollectionEquivalence
import Hypernets.Copying.CopyingTemplateLaws

/-! The copying/garbage-collection correction needed by private readback.
After copying a closed payload through a one-input tree, the unused retained
copy is a literal GC instance; no sharing edge is declared to be an identity. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ClosedCopy
open Graph Opening
variable {d} (T : ContractionTree .term 1) (H : Hypernet d [.term] (environmentInterface 0 0))

def collected : Hypernet d [] (environmentInterface 0 0) := GarbageCollection.right d 0 0

def copies : Hypernet d [.term] (environmentInterface (0*2) (0*2)) :=
  (Net.Parallel.net (Net.Tensor.family H (collected (d := d)))
    (CopyRule.pairBoundary 0 0 0) ⟨[false,true],by intro b; cases b <;> simp⟩).reboundary
      (by simp) (by simp [environmentInterface])

def corrected : Hypernet d [.term] (environmentInterface 0 0) :=
  Serial.net (copies H) (Translation.environmentDistributor d 0 0 2)

/-- The only changed branch is the whole actual nullary retained copy. -/
noncomputable def witness (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness GarbageCollection.template (CopyRule.after T H) (corrected H) := by
  apply FillingWitness.serial
  · apply FillingWitness.reboundary
    apply FillingWitness.parallel (CopyRule.pairBoundary 0 0 0)
    intro b
    cases b
    · exact FillingWitness.refl H free
    · exact FillingWitness.of_rel 0 (GarbageCollection.literal (CopyRule.residualTree T) H copyable free)
  · exact FillingWitness.refl _
      (Translation.allLabels_tensor _
        (Distributor.allLabels_atDepth _ .term 0 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
        (Distributor.allLabels_atDepth _ .atom 0 2 d (by intro m eq; cases eq) (by intro m eq; cases eq)))

/-- The active copy remains a complete actual component of the corrected graph. -/
noncomputable def occurrence : Occurrence H (corrected H) :=
  (BoxPullWeakening.RetainedCopy.targetCast
    (Occurrence.ParallelJoin.component (Net.Tensor.family H (collected (d := d)))
      (CopyRule.pairBoundary 0 0 0) ⟨[false,true],by intro b; cases b <;> simp⟩ false)
    (by simp) (by simp [environmentInterface])).comp
    (BoxPullWeakening.ReverseComponents.serialLeft _ _)

theorem input (i : Fin [Wire.term].length) :
    (occurrence H).ports (.input i) = .input i := by
  change Fin 1 at i
  have zero : i=0 := Subsingleton.elim _ _
  subst i
  cases d <;> rfl

theorem cover (e : (corrected H).Edge) : ∃ a, (occurrence H).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨b,e⟩
    cases b
    · rcases e with ⟨b,e⟩
      cases b
      · exact ⟨e,rfl⟩
      · rcases e with ⟨b,e⟩
        cases b <;> exact Fin.elim0 e.1
    · rcases e with ⟨b,e⟩
      cases b <;> exact Fin.elim0 e.1

/-- Zero-resource distributors and the collected closed branch contain no
edges, so the complete active occurrence gives an exact graph isomorphism. -/
noncomputable def iso : DeepIso H (corrected H) :=
  (occurrence H).iso_of_edge_surjective (input H) (fun i => Fin.elim0 i) (cover H)

/-- A genuine GC filling relates the exact original copy reduct to its active
closed payload, for every concrete one-input contraction-tree presentation. -/
noncomputable def garbage (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness GarbageCollection.template (CopyRule.after T H) H :=
  (witness T H copyable free).congr (DeepIso.refl _) (iso H).symm

end Hypernets.Copying.Parametricity.ClosedCopy

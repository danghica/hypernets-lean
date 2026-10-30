import Hypernets.Copying.ParametricityClosedCopy
import Hypernets.Copying.CopyingInputContext
import Hypernets.Copying.AddressedWitness
import Hypernets.Copying.CopyingSelectedInput

/-! The two closed copies produced by private readback are separated by two
genuine template fillings: copying of the retained branch, followed by garbage
collection. The final graph is the actual ordered tensor of the two payloads. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ClosedCopyPair
open Graph Opening
variable {d} (H : Hypernet d [.term] (environmentInterface 0 0))

def graph (K : Hypernet d [.term] (environmentInterface 0 0)) :
    Hypernet d [.term,.term] (environmentInterface 0 0) :=
  CopyingDouble.afterWith (n := 0) H K

/-- Keep the active copy and the literal zero-resource distributor, while
replacing only the retained closed branch by its certified filling. -/
noncomputable def rightWitness {P : PreTemplate}
    {G K : Hypernet d [.term] (environmentInterface 0 0)}
    (free : FocusFree H) (w : FillingWitness P G K) :
    FillingWitness P (graph H G) (graph H K) := by
  apply FillingWitness.serial
  · apply FillingWitness.reboundary
    apply FillingWitness.parallel (CopyRule.pairBoundary 1 0 0)
    intro b; cases b
    · exact FillingWitness.refl H free
    · exact w
  · exact FillingWitness.refl _
      (Translation.allLabels_tensor _
        (Distributor.allLabels_atDepth _ .term 0 2 d (by intro m eq; cases eq) (by intro m eq; cases eq))
        (Distributor.allLabels_atDepth _ .atom 0 2 d (by intro m eq; cases eq) (by intro m eq; cases eq)))

/-- The second copy is exactly the original copying template on the complete
residual one-input tree, including its newly inserted weakening. -/
noncomputable def copying (T : ContractionTree .term 2)
    (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template (CopyRule.after T H)
      (graph H (CopyRule.after (CopyRule.residualTree T) H)) :=
  rightWitness H free (FillingWitness.of_rel 0
    (CopyingTemplate.literal (CopyRule.residualTree T) H copyable free))

/-- Each of the two payloads is a complete occurrence of the corrected graph. -/
noncomputable def component (b : Bool) : Occurrence (Net.Tensor.family H H b) (graph H H) :=
  (BoxPullWeakening.RetainedCopy.targetCast
    (Occurrence.ParallelJoin.component (Net.Tensor.family H H)
      (CopyRule.pairBoundary 1 0 0) ⟨[false,true],by intro b; cases b <;> simp⟩ b)
    (by simp : _ = [Wire.term,Wire.term]) (by simp [environmentInterface] : _ = environmentInterface 0 0)).comp
    (BoxPullWeakening.ReverseComponents.serialLeft _ (Translation.environmentDistributor d 0 0 2))

theorem disjoint (a b : Bool) (ne : a ≠ b)
    (e : (Net.Tensor.family H H a).Edge) (c : (Net.Tensor.family H H b).Edge) :
    (component H a).edges e ≠ (component H b).edges c := by
  intro eq
  cases d
  all_goals
    have eq := eq_of_heq (Sigma.mk.inj eq).2
    exact ne (congrArg Sigma.fst eq)

/-- Assemble the actual independent payload occurrences with the tensor's
original input order; no machine transition is used by this isomorphism. -/
noncomputable def occurrence : Occurrence (Net.Tensor.net H H) (graph H H) :=
  Occurrence.ParallelJoin.occurrence (Net.Tensor.family H H)
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (component H) (disjoint H)

theorem input (i : Fin [Wire.term,Wire.term].length) :
    (occurrence H).ports (.input i) = .input i := by
  change Fin 2 at i
  have cases : i=0 ∨ i=1 := by omega
  rcases cases with rfl | rfl
  all_goals cases d <;> rfl

theorem cover (e : (graph H H).Edge) : ∃ a, (occurrence H).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨b,e⟩
    cases b
    · exact ⟨e,rfl⟩
    · rcases e with ⟨b,e⟩
      cases b <;> exact Fin.elim0 e.1

noncomputable def iso : DeepIso (Net.Tensor.net H H) (graph H H) :=
  (occurrence H).iso_of_edge_surjective (input H) (fun i => Fin.elim0 i) (cover H)

/-- Collect the unused retained copy and remove only the genuinely empty
distributor carriers, obtaining the two original ordered payloads. -/
noncomputable def garbage (T : ContractionTree .term 2)
    (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness GarbageCollection.template
      (graph H (CopyRule.after (CopyRule.residualTree T) H)) (Net.Tensor.net H H) :=
  (rightWitness H free (ClosedCopy.garbage (CopyRule.residualTree T) H copyable free)).congr
    (DeepIso.refl _) (iso H).symm

end Hypernets.Copying.Parametricity.ClosedCopyPair

namespace Hypernets.Copying.FillingWitness
open Graph

/-- Input reindexing is the actual one-hole context, hence preserves each
existing filling certificate without adding a certificate constructor. -/
noncomputable def inputPermuted {P : PreTemplate} {d I O}
    {G H : Hypernet d I O} (w : FillingWitness P G H) (p : TypedPermutation I) :
    FillingWitness P (CopyingInputPermutation.net G p) (CopyingInputPermutation.net H p) := by
  let C := CopyingInputPermutation.frame d I O p
  have free : FocusFree C := by
    cases d <;> intro e
    all_goals
      change ∀ m, Primitive.hole ⟨0,I,O⟩ ≠ Primitive.focus m
      intro m eq; cases eq
  have lifted := FillingWitness.plug C free (CopyingInputPermutation.frameEdge d I O p)
    (w.reboundary (by cases d <;> rfl) (by cases d <;> rfl))
  exact lifted.congr (CopyingInputPermutation.frameIso G p) (CopyingInputPermutation.frameIso H p)

end Hypernets.Copying.FillingWitness

namespace Hypernets.Copying.Parametricity.ClosedCopyPair
open Graph
variable {d} (T : ContractionTree .term 2)
    (H : Hypernet d [.term] (environmentInterface 0 0)) (i : Fin 2)

/-- The intermediate graph keeps the original selected-input compensation.
In private readback the selected input is one, not the store's input zero. -/
noncomputable def selectedMiddle : Hypernet d [.term,.term] [] :=
  CopyingInputPermutation.net
    (graph H (CopyRule.after
      (CopyRule.residualTree (CopyingInputPermutation.reordered T
        (CopyingSelectedInput.permutation (n := 1) i))) H))
    (CopyingSelectedInput.permutation (n := 1) i).symm

def selectedPair : Hypernet d [.term,.term] [] :=
  CopyingInputPermutation.net (Net.Tensor.net H H) (CopyingSelectedInput.permutation (n := 1) i).symm

/-- A genuine copying filling at either original input, retaining the ordered
boundary action of the actual selected-input rewrite. -/
noncomputable def selectedCopying (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template (CopyingSelectedInput.after T H i)
      (selectedMiddle T H i) :=
  (copying H (CopyingInputPermutation.reordered T (CopyingSelectedInput.permutation (n := 1) i))
    copyable free).inputPermuted (CopyingSelectedInput.permutation (n := 1) i).symm

/-- A separate genuine garbage-collection filling completes the selected
two-copy correction; no transitivity of filling certificates is asserted. -/
noncomputable def selectedGarbage (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness GarbageCollection.template (selectedMiddle T H i) (selectedPair H i) :=
  (garbage H (CopyingInputPermutation.reordered T (CopyingSelectedInput.permutation (n := 1) i))
    copyable free).inputPermuted (CopyingSelectedInput.permutation (n := 1) i).symm

end Hypernets.Copying.Parametricity.ClosedCopyPair

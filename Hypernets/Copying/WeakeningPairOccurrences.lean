import Hypernets.Copying.WeakeningTranslationSteps
import Hypernets.Copying.DistributorExtension
import Hypernets.Copying.WeakeningRowPartition

/-! Independent operands of the original Figure 16 pair, with their common
unused resource exposed. Equality transport changes no graph component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Pair
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (payload payload_input payload_output outputIndex serialLeftOccurrence)

/-- Original pair with its output equality exposed as boundary transport. -/
def paired {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d [.term,.term] (environmentInterface (k*2) (h*2)) :=
  (Net.Parallel.net (Net.Tensor.family G H) (Translation.pairBoundary k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩).reboundary rfl
      (by simp [environmentInterface,Nat.mul_two])

theorem original_pair {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) :
    Translation.pair G H = paired G H := cast_eq_reboundary _ _ _

/-- The complete pair followed by its actual binary resource distributor. -/
def core {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d [.term,.term] (environmentInterface k h) :=
  Serial.net (paired G H) (Translation.environmentDistributor d k h 2)

/-- Either original operand occurs in the ordered pair, with full labels. -/
def component {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) (b : Bool) :
    Occurrence (Net.Tensor.family G H b) (paired G H) :=
  (Occurrence.ParallelJoin.component (Net.Tensor.family G H) (Translation.pairBoundary k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩ b).reboundaryTarget rfl
      (by simp [environmentInterface,Nat.mul_two])

theorem component_output {d k h} (G H : Hypernet d [.term] (environmentInterface k h))
    (b : Bool) (i : Fin (environmentInterface k h).length) :
    (component G H b).ports (.output ⟨i.val,by cases b <;> exact i.isLt⟩) = .output (PairBoundary.index b i) := by cases b <;> rfl

theorem component_input {d k h} (G H : Hypernet d [.term] (environmentInterface k h))
    (b : Bool) (i : Fin 1) :
    (component G H b).ports (.input ⟨i.val,by cases b <;> exact i.isLt⟩) = .input ⟨PairBoundary.use b,by cases b <;> decide⟩ := by
  have z : i = 0 := Subsingleton.elim _ _
  subst i
  cases b <;> rfl

variable {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

/-- Retain each independently supplied operand in its extended pair. -/
def oldComponent (b : Bool) :
    Occurrence (Net.Tensor.family G H b) (paired (extend G s) (extend H s)) :=
  match b with
  | false => (payload G s).comp (component (extend G s) (extend H s) false)
  | true => (payload H s).comp (component (extend G s) (extend H s) true)

theorem components_disjoint : ∀ a b, a ≠ b → ∀ e c,
    (oldComponent G H s a).edges e ≠ (oldComponent G H s b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · cases eq
  · cases eq
  · exact ne rfl

/-- The whole old pair is retained; no equality between the two operands is used. -/
noncomputable def oldPair : Occurrence (paired G H) (paired (extend G s) (extend H s)) :=
  (Occurrence.ParallelJoin.occurrence (Net.Tensor.family G H) (Translation.pairBoundary k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (oldComponent G H s)
    (components_disjoint G H s)).reboundarySource rfl (by simp [environmentInterface,Nat.mul_two])

theorem oldPair_component (b : Bool) (v : (Net.Tensor.family G H b).Vertex) :
    (oldPair G H s).ports ((component G H b).ports v) = (oldComponent G H s b).ports v := by
  unfold oldPair component
  simp only [Occurrence.reboundaryTarget]
  rw [Occurrence.reboundarySource_ports]
  simp only [Occurrence.ParallelJoin.component]
  exact Occurrence.ParallelJoin.occurrence_embed _ _ _ _ _ b v

theorem oldPair_output (b : Bool) (i : Fin (environmentInterface k h).length) :
    (oldPair G H s).ports (.output (PairBoundary.index b i)) =
      .output (PairBoundary.index b (outputIndex s i)) := by
  have law := oldPair_component G H s b (.output ⟨i.val,by cases b <;> exact i.isLt⟩)
  rw [component_output] at law
  cases b
  · change _ = (component (extend G s) (extend H s) false).ports ((payload G s).ports (.output i)) at law
    rw [payload_output] at law
    exact law.trans (component_output (extend G s) (extend H s) false (outputIndex s i))
  · change _ = (component (extend G s) (extend H s) true).ports ((payload H s).ports (.output i)) at law
    rw [payload_output] at law
    exact law.trans (component_output (extend G s) (extend H s) true (outputIndex s i))

theorem oldPair_input (i : Fin 2) : (oldPair G H s).ports (.input i) = .input i := by
  have cases_i : i = 0 ∨ i = 1 := by
    by_cases z : i.val = 0
    · exact .inl (Fin.ext z)
    · exact .inr (Fin.ext (by have := i.isLt; omega))
  rcases cases_i with rfl | rfl
  · have law := oldPair_component G H s false (.input ⟨0,by decide⟩)
    erw [component_input G H false (0 : Fin 1)] at law
    change _ = (component (extend G s) (extend H s) false).ports ((payload G s).ports (.input 0)) at law
    rw [payload_input] at law
    exact law.trans (component_input (extend G s) (extend H s) false (0 : Fin 1))
  · have law := oldPair_component G H s true (.input ⟨0,by decide⟩)
    erw [component_input G H true (0 : Fin 1)] at law
    change _ = (component (extend G s) (extend H s) true).ports ((payload H s).ports (.input 0)) at law
    rw [payload_input] at law
    exact law.trans (component_input (extend G s) (extend H s) true (0 : Fin 1))

/-- The retained pair and retained distributor in the enlarged complete graph. -/
noncomputable def oldLeft : Occurrence (paired G H) (core (extend G s) (extend H s)) :=
  (oldPair G H s).comp (serialLeftOccurrence _ _)

noncomputable def oldRight : Occurrence (Translation.environmentDistributor d k h 2)
    (core (extend G s) (extend H s)) :=
  (BoxPullWeakening.RetainedCopy.distributor d k h s).comp (Occurrence.serialRight _ _)

theorem old_boundary (i : Fin (environmentInterface (k*2) (h*2)).length) :
    (oldLeft G H s).ports (.output i) = (oldRight G H s).ports (.input i) := by
  obtain ⟨b,j,rfl⟩ := PairBoundary.index_surjective i
  change BoundarySerial.leftInsert _ _ ((oldPair G H s).ports (.output _)) =
    BoundarySerial.rightInsert _ _ ((BoxPullWeakening.RetainedCopy.distributor d k h s).ports (.input _))
  rw [oldPair_output,BoxPullWeakening.RetainedCopy.distributor_pair_input,
    CopyRule.serial_left_output,CopyRule.serial_right_input]

theorem old_disjoint : ∀ e c, (oldLeft G H s).edges e ≠ (oldRight G H s).edges c := by
  cases d <;> intro e c eq <;> cases eq

/-- Both old operands and all old rows form a complete-label occurrence. -/
noncomputable def old : Occurrence (core G H) (core (extend G s) (extend H s)) :=
  Occurrence.SerialJoin.occurrence (oldLeft G H s) (oldRight G H s)
    (old_boundary G H s) (old_disjoint G H s)

theorem old_input (i : Fin 2) : (old G H s).ports (.input i) = .input i := by
  unfold old
  rw [Occurrence.SerialJoin.occurrence_input]
  change BoundarySerial.leftInsert _ _ ((oldPair G H s).ports (.input i)) = _
  rw [oldPair_input]
  exact Combined.left_input (paired (extend G s) (extend H s))
    (Translation.environmentDistributor d (variables s k) (atoms s h) 2) i

theorem old_output (i : Fin (environmentInterface k h).length) :
    (old G H s).ports (.output i) = .output (outputIndex s i) := by
  unfold old
  rw [Occurrence.SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert _ _ ((BoxPullWeakening.RetainedCopy.distributor d k h s).ports (.output i)) = _
  rw [BoxPullWeakening.RetainedCopy.distributor_output,Application.right_serial_output]

end Hypernets.Copying.Weakening.Pair

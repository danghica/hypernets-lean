import Hypernets.Copying.CopyingMergeRetainedIso
import Hypernets.Copying.CopyingMergeResources
import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! The actual active and retained abstraction occurrences after one original
copy, with an arbitrary retained input graph (including zero inputs). -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyComponents
open Graph Opening
variable {d a k h : Nat}
    (P : Hypernet d (List.replicate a .term) [.term])
    (H : Hypernet d [.term] (environmentInterface k h))

abbrev target : Hypernet d (List.replicate (a+1) .term) (environmentInterface k h) := (CopyingMerge.net (a := 1) H (Serial.net P H)).reboundary
  (by rw [Nat.add_comm]) rfl

noncomputable def branch (side : Bool) :
    Occurrence (Net.Tensor.family H (Serial.net P H) side) (target P H) :=
  (CopyingMerge.component (a := 1) H (Serial.net P H) side).reboundaryTarget (by rw [Nat.add_comm]) rfl
noncomputable def active : Occurrence H (target P H) := branch P H false
noncomputable def retained : Occurrence H (target P H) :=
  (Occurrence.serialRight P H).comp (branch P H true)
noncomputable def upstream : Occurrence P (target P H) :=
  (BoxPullWeakening.ReverseComponents.serialLeft P H).comp (branch P H true)
noncomputable def distributor : Occurrence (Translation.environmentDistributor d k h 2) (target P H) :=
  (Occurrence.serialRight _ _).reboundaryTarget (by rw [Nat.add_comm]) rfl

noncomputable def payload (side : Bool) : Occurrence (Net.Tensor.family H H side) (target P H) := by
  cases side
  · exact active P H
  · exact retained P H

theorem payload_disjoint : ∀ side other, side ≠ other → ∀ e f,
    (payload P H side).edges e ≠ (payload P H other).edges f := by
  intro side other ne e f eq
  cases side <;> cases other
  all_goals first | exact False.elim (ne rfl) | (cases d <;> cases eq)

/-- The complete two-payload graph occurs before the original complete
resource distributor. Neither copy's recursively boxed body is modified. -/
noncomputable def pair : Occurrence (CopyingMerge.pair (a := 1) (b := 1) H H) (target P H) :=
  (Occurrence.ParallelJoin.occurrence (Net.Tensor.family H H) (CopyingMerge.boundary 1 1 k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (payload P H) (payload_disjoint P H)).reboundarySource
      (by simp) (by simp [environmentInterface,Nat.mul_two])

theorem pair_component (side : Bool) (v : (Net.Tensor.family H H side).Vertex) :
    (pair P H).ports ((CopyingMerge.pairComponent (a := 1) (b := 1) H H side).ports v) =
      (payload P H side).ports v := by
  change Occurrence.ParallelJoin.ports _ _ _ _
    (Port.cast (by simp) (by simp [environmentInterface,Nat.mul_two])
      (Port.cast (by simp) (by simp [environmentInterface,Nat.mul_two])
        (Net.Parallel.embed _ _ side v))) = _
  have cancel : ∀ w : Port (Σ side : Bool, (Net.Tensor.family H H side).Internal)
      (List.replicate 1 Wire.term ++ List.replicate 1 Wire.term).length
      (((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
        (List.replicate h Wire.atom ++ List.replicate h Wire.atom))).length, Port.cast
      (by simp :
        List.replicate (1+1) Wire.term = List.replicate 1 Wire.term ++ List.replicate 1 Wire.term)
      (by simp [environmentInterface,Nat.mul_two] : environmentInterface (k*2) (h*2) =
        ((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
          (List.replicate h Wire.atom ++ List.replicate h Wire.atom)))
      (Port.cast (by simp)
        (by simp [environmentInterface,Nat.mul_two]) w) = w := by
    intro w; cases w <;> rfl
  rw [cancel]
  exact Occurrence.ParallelJoin.embed_ports _ _ _ _ side v

private theorem copyOutput_surjective (i : Fin (environmentInterface (k*2) (h*2)).length) :
    ∃ side : Bool, ∃ j : Fin (environmentInterface k h).length, CopyRule.copyOutput k h side j = i := by
  let old : Fin (((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
      (List.replicate h Wire.atom ++ List.replicate h Wire.atom))).length :=
    Fin.cast (by simp [environmentInterface,Nat.mul_two]) i
  have onto := (Translation.pairBoundary k h).outputs.right_inv old
  generalize selected : (Translation.pairBoundary k h).outputs.invFun old = x at onto
  rcases x with ⟨side,j⟩
  cases side
  · refine ⟨false,j,?_⟩
    apply Fin.ext
    exact congrArg (fun z => z.val) onto
  · refine ⟨true,j,?_⟩
    apply Fin.ext
    exact congrArg (fun z => z.val) onto

theorem pair_output (i : Fin (environmentInterface (k*2) (h*2)).length) :
    (pair P H).ports (.output i) = (distributor P H).ports (.input i) := by
  obtain ⟨side,j,rfl⟩ := copyOutput_surjective i
  rw [← CopyingMerge.pair_output (a := 1) (b := 1) H H side j,pair_component]
  cases side
  · cases d <;> rfl
  · change (branch P H true).ports (BoundarySerial.rightInsert P H (.output j)) = _
    rw [Application.right_serial_output]
    cases d <;> rfl

theorem pair_distributor_disjoint : ∀ e f, (pair P H).edges e ≠ (distributor P H).edges f := by
  cases d <;> rintro ⟨side,e⟩ f eq <;> cases side <;> cases eq

/-- The literal merged two-copy graph, with every canonical output row,
occurs inside the original target; only its retained input tree lies outside. -/
noncomputable def duplicate : Occurrence (CopyingMerge.net (a := 1) (b := 1) H H) (target P H) :=
  Occurrence.SerialJoin.occurrence (pair P H) (distributor P H)
    (pair_output P H) (pair_distributor_disjoint P H)

theorem duplicate_input (side : Bool) :
    (duplicate P H).ports (.input (if side then ⟨1,by simp⟩ else ⟨0,by simp⟩)) =
      (payload P H side).ports (.input (by cases side <;> exact (0 : Fin 1))) := by
  unfold duplicate
  rw [Occurrence.SerialJoin.occurrence_input]
  have eq : (CopyingMerge.pairComponent (a := 1) (b := 1) H H side).ports (.input (by cases side <;> exact (0 : Fin 1))) =
      .input (if side then ⟨1,by simp⟩ else ⟨0,by simp⟩) := by cases side <;> rfl
  rw [← eq,pair_component]

theorem upstream_link : (upstream P H).ports (.output 0) =
    (duplicate P H).ports (.input ⟨1,by simp⟩) := by
  rw [show (⟨1,by simp⟩ : Fin (List.replicate (1+1) Wire.term).length) =
    (if true then ⟨1,by simp⟩ else ⟨0,by simp⟩) from rfl,duplicate_input]
  change (branch P H true).ports (BoundarySerial.leftInsert P H (.output 0)) =
    (branch P H true).ports (BoundarySerial.rightInsert P H (.input 0))
  exact congrArg _ (BoxPullWeakening.ReverseComponents.serial_boundary P H 0)

theorem upstream_duplicate_disjoint : ∀ e f, (upstream P H).edges e ≠ (duplicate P H).edges f := by
  cases d <;> intro e f eq
  all_goals
    rcases f with ⟨side,f⟩
    cases side
    · rcases f with ⟨copy,f⟩; cases copy <;> cases eq
    · cases eq

theorem upstream_input (i : Fin (List.replicate a Wire.term).length) :
    (upstream P H).ports (.input i) = .input ⟨i.val+1,by
      have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  change Port.cast (by rw [Nat.add_comm]) rfl ((CopyingMerge.component (a := 1) H (Serial.net P H) true).ports
    (BoundarySerial.leftInsert P H (.input i))) = _
  rw [Combined.left_input,CopyingMerge.right_input]
  exact congrArg Port.input (Fin.ext (by change 1+i.val=i.val+1; omega))

theorem active_input : (active P H).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change Port.cast (by rw [Nat.add_comm]) rfl ((CopyingMerge.component (a := 1) H (Serial.net P H) false).ports (.input (0 : Fin 1))) = _
  rw [CopyingMerge.left_input]
  rfl

theorem duplicate_output (i : Fin (environmentInterface k h).length) :
    (duplicate P H).ports (.output i) = .output i := by
  unfold duplicate
  rw [Occurrence.SerialJoin.occurrence_output]
  change Port.cast (by rw [Nat.add_comm]) rfl (BoundarySerial.rightInsert _ _ (.output i)) = _
  rw [Application.right_serial_output]
  rfl

end Hypernets.Copying.Parametricity.CopyComponents

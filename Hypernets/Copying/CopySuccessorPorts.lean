import Hypernets.Copying.CopySuccessorLocalMatch

/-! Incidence attachments for the unchanged copy construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

theorem serial_left_output {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) (i : Fin J.length) :
    BoundarySerial.leftInsert A B (.output i) = .internal (.inl i) := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J K).targetPort false i) = _
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

theorem serial_right_input {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) (i : Fin J.length) :
    BoundarySerial.rightInsert A B (.input i) = .internal (.inl i) := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J K).sourcePort true i) = _
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    rfl

variable {d n k h} (T : ContractionTree .term (n+1)) (H : Hypernet d [.term] (environmentInterface k h))

def pairInsert (b : Bool) (p : (Net.Tensor.family H (Serial.net (residual T d) H) b).Vertex) : (copies T H).Vertex :=
  Port.cast (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])
    (Net.Parallel.embed (Net.Tensor.family H (Serial.net (residual T d) H)) (pairBoundary n k h) b p)

def activeInsert (p : H.Vertex) : (after T H).Vertex :=
  BoundarySerial.leftInsert (copies T H) (Translation.environmentDistributor d k h 2) (pairInsert T H false p)
def retainedInsert (p : H.Vertex) : (after T H).Vertex :=
  BoundarySerial.leftInsert (copies T H) (Translation.environmentDistributor d k h 2)
    (pairInsert T H true (BoundarySerial.rightInsert (residual T d) H p))
def treeInsert (p : T.net.Vertex) : (after T H).Vertex :=
  BoundarySerial.leftInsert (copies T H) (Translation.environmentDistributor d k h 2)
    (pairInsert T H true (BoundarySerial.leftInsert (residual T d) H
      (Net.Expansion.insert (residualFrame n) (residualFill T) true p)))

theorem pair_output (b : Bool) (i : Fin (environmentInterface k h).length) :
    pairInsert T H b (.output (by cases b <;> exact i)) = .output (copyOutput k h b i) := by
  cases d <;> cases b <;>
    simp only [pairInsert,Net.Parallel.embed,Port.cast,pairBoundary,copyOutput]
  all_goals exact congrArg Port.output (Fin.ext rfl)

theorem pair_left_input : pairInsert T H false (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := by
  cases d
  all_goals
    simp only [pairInsert,Net.Parallel.embed,Port.cast,pairBoundary,Net.Tensor.ports,Net.Tensor.join]
    exact congrArg Port.input (Fin.ext rfl)

theorem pair_right_input (i : Fin (List.replicate n Wire.term).length) :
    pairInsert T H true (.input i) = .input ⟨i.val+1,by have := i.isLt; simp at *;omega⟩ := by
  cases d
  all_goals
    simp only [pairInsert,Net.Parallel.embed,Port.cast,pairBoundary,Net.Tensor.ports,Net.Tensor.join]
    apply congrArg Port.input
    apply Fin.ext
    change 1+i.val=i.val+1
    omega

theorem active_port (p : H.Vertex) : Port.map (successorVertices T H) (activeInsert T H p) =
    SuccessorMatch.copyPort (G := before T H) (v := .input ⟨0,by simp⟩) p := by
  cases p with
  | internal x => cases d <;> rfl
  | input i =>
    have eq : i = 0 := by apply Fin.ext; change i.val = 0; have := i.isLt; change i.val < 1 at this; omega
    subst i
    unfold activeInsert
    rw [pair_left_input,Combined.left_input]
    rfl
  | output i =>
    unfold activeInsert
    rw [pair_output,serial_left_output]
    cases d <;> rfl

theorem retained_internal (x : H.Internal) : Port.map (successorVertices T H) (retainedInsert T H (.internal x)) =
    Port.map Sum.inl (BoundarySerial.rightInsert (tree T d) H (.internal x)) := by cases d <;> rfl

theorem retained_input (i : Fin 1) : Port.map (successorVertices T H) (retainedInsert T H (.input i)) =
    Port.map Sum.inl (BoundarySerial.rightInsert (tree T d) H (.input i)) := by
  have eq : i = 0 := by apply Fin.ext; omega
  subst i
  cases d <;> rfl

theorem retained_output (i : Fin (environmentInterface k h).length) :
    Port.map (successorVertices T H) (retainedInsert T H (.output i)) =
      SuccessorMatch.linkPort (G := before T H) (H := H) (copyOutput k h true i) := by
  unfold retainedInsert
  rw [Application.right_serial_output,pair_output,serial_left_output]
  cases d <;> rfl

theorem tree_internal (x : T.net.Internal) : Port.map (successorVertices T H) (treeInsert T H (.internal x)) =
    Port.map Sum.inl (BoundarySerial.leftInsert (tree T d) H (.internal x)) := by cases d <;> rfl

theorem tree_output (i : Fin 1) : Port.map (successorVertices T H) (treeInsert T H (.output i)) =
    Port.map Sum.inl (BoundarySerial.leftInsert (tree T d) H (.output i)) := by
  have eq : i = 0 := by apply Fin.ext; omega
  subst i
  cases d <;> rfl

theorem tree_zero : Port.map (successorVertices T H) (treeInsert T H (.input ⟨0,by simp⟩)) =
    SuccessorMatch.weakPort (G := before T H) (H := H) := by cases d <;> rfl

theorem residual_succ (i : Fin n) :
    Net.Expansion.insert (residualFrame n) (residualFill T) true
      (.input ⟨i.val+1,by simpa [residualFrame,residualLabel,treeHole,primitiveSignature] using Nat.succ_lt_succ i.isLt⟩) = .input ⟨i.val,by simpa using i.isLt⟩ := by
  change Port.map Sum.inl ((residualFrame n).sourcePort true _) = _
  simp only [Net.sourcePort,residualFrame,residualSource,List.getElem_cons_succ,List.getElem_map,List.getElem_finRange,Port.map]
  rfl

theorem tree_succ (i : Fin n) : Port.map (successorVertices T H)
    (treeInsert T H (.input ⟨i.val+1,by simpa using Nat.succ_lt_succ i.isLt⟩)) =
      Port.map Sum.inl (BoundarySerial.leftInsert (tree T d) H (.input ⟨i.val+1,by simpa using Nat.succ_lt_succ i.isLt⟩)) := by
  unfold treeInsert
  rw [residual_succ]
  cases d
  all_goals
    change Port.map (successorVertices T H) (BoundarySerial.leftInsert _ _
      (pairInsert T H true (BoundarySerial.leftInsert (residual T _) H (.input _)))) = _
    rw [Combined.left_input,pair_right_input,Combined.left_input,Combined.left_input]
    rfl
end Hypernets.Copying.CopyRule

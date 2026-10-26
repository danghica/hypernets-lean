import Hypernets.Copying.CopyFrames

/-! The literal Figure 17 rule, with arbitrary residual term inputs and both
ordered output distributors. This is separate from the linear compute relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

/-- Exchange the middle output blocks while preserving the external input order. -/
def pairBoundary (n k h : Nat) :
    Net.Parallel.Boundary (Net.Tensor.interfaces [Wire.term] (List.replicate n Wire.term))
      (Net.Tensor.interfaces (environmentInterface k h) (environmentInterface k h))
      ([Wire.term] ++ List.replicate n Wire.term)
      ((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
        (List.replicate h Wire.atom ++ List.replicate h Wire.atom)) where
  inputs := Net.Tensor.ports _ _
  outputs := (Translation.pairBoundary k h).outputs
  input_label := Net.Tensor.join_label _ _
  output_label := (Translation.pairBoundary k h).output_label

/-- The active copy is leftmost. The retained tree feeds the second copy. -/
def copies {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (n+1) .term) (environmentInterface (k*2) (h*2)) :=
  (Net.Parallel.net (Net.Tensor.family H (Serial.net (residual T d) H))
      (pairBoundary n k h) ⟨[false,true],by intro b; cases b <;> simp⟩).reboundary
      (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

def before {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (n+1) .term) (environmentInterface k h) := Serial.net (tree T d) H

def after {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (n+1) .term) (environmentInterface k h) :=
  Serial.net (copies T H) (Translation.environmentDistributor d k h 2)

/-- Copyability is mandatory; stability is not substituted for it. -/
inductive Rule : {d n k h : Nat} →
    Hypernet d (List.replicate (n+1) .term) (environmentInterface k h) →
    Hypernet d (List.replicate (n+1) .term) (environmentInterface k h) → Prop where
  | copy {d n k h} (T : ContractionTree .term (n+1))
      (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) :
      Rule (before T H) (after T H)

theorem rule_iff {d n k h} {L R : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)} :
    Rule L R ↔ ∃ T H, Copyable H ∧ L = before (d := d) (k := k) (h := h) T H ∧ R = after T H := by
  constructor
  · intro s; cases s with | copy T H c => exact ⟨T,H,c,rfl,rfl⟩
  · rintro ⟨T,H,c,rfl,rfl⟩; exact .copy T H c

def leftEdge {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (e : H.Edge) : (after T H).Edge :=
  Serial.leftEdge _ _ ⟨false,e⟩
def rightEdge {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (e : H.Edge) : (after T H).Edge :=
  Serial.leftEdge _ _ ⟨true,Serial.rightEdge _ _ e⟩

/-- Duplication preserves the complete label, including literal nested box bodies. -/
theorem copy_labels {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (e : H.Edge) :
    (after T H).edgeLabel (leftEdge T H e) = H.edgeLabel e ∧
    (after T H).edgeLabel (rightEdge T H e) = H.edgeLabel e := by cases d <;> exact ⟨rfl,rfl⟩

/-- The copies have disjoint edge carriers even when their labels are identical. -/
theorem copies_disjoint {d n k h} (T : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (e f : H.Edge) :
    leftEdge T H e ≠ rightEdge T H f := by
  cases d <;> intro eq
  all_goals
    have inner := eq_of_heq (Sigma.mk.inj eq).2
    have bad := congrArg Sigma.fst inner
    cases bad
end Hypernets.Copying.CopyRule

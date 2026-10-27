import Hypernets.Copying.BoxPermutationOpening

/-! Boundary actions through the literal two-copy reduct and its distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoundaryIso
open Graph

def reboundary {d I O J K} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (hi : I = J) (ho : O = K) : BoundaryIso (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  exact {
    ports := f.ports
    edges := f.edges
    vertex_label := f.vertex_label
    input_iff := f.input_iff
    output_iff := f.output_iff
    edge_label := f.edge_label
    source := by intro e; simpa only [Net.reboundary,Port.cast_refl_fun,List.map_id] using f.source e
    target := by intro e; simpa only [Net.reboundary,Port.cast_refl_fun,List.map_id] using f.target e }

theorem reboundary_edges {d I O J K} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (hi : I = J) (ho : O = K) : (f.reboundary hi ho).edges = f.edges := by
  cases hi; cases ho; rfl

theorem reboundary_input {d I O J K} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (hi : I = J) (ho : O = K) (a b : Fin I.length) (eq : f.ports.toFun (.input a) = .input b) :
    (f.reboundary hi ho).ports.toFun (.input (Fin.cast (congrArg List.length hi) a)) =
      .input (Fin.cast (congrArg List.length hi) b) := by
  cases hi; cases ho; exact eq

theorem reboundary_output {d I O J K} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (hi : I = J) (ho : O = K) (a b : Fin O.length) (eq : f.ports.toFun (.output a) = .output b) :
    (f.reboundary hi ho).ports.toFun (.output (Fin.cast (congrArg List.length ho) a)) =
      .output (Fin.cast (congrArg List.length ho) b) := by
  cases hi; cases ho; exact eq
end Hypernets.Copying.BoundaryIso

namespace Hypernets.Copying.CopyRule.Boundary
open Graph
variable {d n k h} (T : ContractionTree .term (n+1))
    {G H : Hypernet d [.term] (environmentInterface k h)} (f : BoundaryIso G H)

/-- The retained branch keeps every residual tree input fixed. -/
def retained : BoundaryIso (Serial.net (residual T d) G) (Serial.net (residual T d) H) :=
  BoundarySerial.iso (BoundaryIso.refl _) f (fun i => (f.input_singleton i).symm)

theorem retained_input (i : Fin (List.replicate n Wire.term).length) :
    (retained T f).ports.toFun (.input i) = .input i :=
  BoundarySerial.iso_input _ _ _ i

theorem retained_output (i : Fin (environmentInterface k h).length) :
    (retained T f).ports.toFun (.output i) = .output (f.outputs.toFun i) :=
  BoundarySerial.iso_output _ _ _ i

def raw : BoundaryIso
    (Net.Parallel.net (Net.Tensor.family G (Serial.net (residual T d) G))
      (pairBoundary n k h) ⟨[false,true],by intro b; cases b <;> simp⟩)
    (Net.Parallel.net (Net.Tensor.family H (Serial.net (residual T d) H))
      (pairBoundary n k h) ⟨[false,true],by intro b; cases b <;> simp⟩) :=
  BoundaryParallel.iso (fun b => match b with | false => f | true => retained T f)
    (pairBoundary n k h) (pairBoundary n k h) _

def copies : BoundaryIso (CopyRule.copies T G) (CopyRule.copies T H) :=
  (raw T f).reboundary _ _

/-- Both copies have the same free action after the original middle-block shuffle. -/
theorem copies_output (b : Bool) (j : Fin (environmentInterface k h).length) :
    (copies T f).ports.toFun (.output (PairBoundary.index b j)) =
      .output (PairBoundary.index b (f.outputs.toFun j)) := by
  cases b
  · have law := BoundaryParallel.embed
      (G := Net.Tensor.family G (Serial.net (residual T d) G))
      (H := Net.Tensor.family H (Serial.net (residual T d) H))
      (fun b => match b with | false => f | true => retained T f)
      (pairBoundary n k h) (pairBoundary n k h) false (.output j)
    rw [f.map_output] at law
    exact (raw T f).reboundary_output _ _ _ _ law
  · have law := BoundaryParallel.embed
      (G := Net.Tensor.family G (Serial.net (residual T d) G))
      (H := Net.Tensor.family H (Serial.net (residual T d) H))
      (fun b => match b with | false => f | true => retained T f)
      (pairBoundary n k h) (pairBoundary n k h) true (.output j)
    change (raw T f).ports.toFun (.output _) =
      Net.Parallel.embed _ (pairBoundary n k h) true ((retained T f).ports.toFun (.output j)) at law
    rw [retained_output] at law
    exact (raw T f).reboundary_output _ _ _ _ law

/-- Input zero and every unselected residual input keep their original positions. -/
theorem copies_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (copies T f).ports.toFun (.input i) = .input i := by
  let j : Fin ([Wire.term] ++ List.replicate n Wire.term).length := Fin.cast (by simp) i
  have eq := Net.Tensor.join_split [Wire.term] (List.replicate n Wire.term) j
  generalize split : Net.Tensor.split [Wire.term] (List.replicate n Wire.term) j = x at eq
  rcases x with ⟨b,x⟩
  have law := BoundaryParallel.embed
    (G := Net.Tensor.family G (Serial.net (residual T d) G))
    (H := Net.Tensor.family H (Serial.net (residual T d) H))
    (fun b => match b with | false => f | true => retained T f)
    (pairBoundary n k h) (pairBoundary n k h) b (.input x)
  cases b
  · change (raw T f).ports.toFun (.input _) =
      Net.Parallel.embed _ (pairBoundary n k h) false (f.ports.toFun (.input x)) at law
    rw [f.map_input] at law
    change (raw T f).ports.toFun (.input (Net.Tensor.join _ _ ⟨false,x⟩)) = .input (Net.Tensor.join _ _ ⟨false,f.inputs.toFun x⟩) at law
    rw [f.input_singleton] at law
    change Net.Tensor.join _ _ ⟨false,x⟩ = j at eq
    rw [eq] at law
    exact (raw T f).reboundary_input _ _ j j law
  · change (raw T f).ports.toFun (.input _) =
      Net.Parallel.embed _ (pairBoundary n k h) true ((retained T f).ports.toFun (.input x)) at law
    rw [retained_input] at law
    change (raw T f).ports.toFun (.input (Net.Tensor.join _ _ ⟨true,x⟩)) = .input (Net.Tensor.join _ _ ⟨true,x⟩) at law
    change Net.Tensor.join _ _ ⟨true,x⟩ = j at eq
    rw [eq] at law
    exact (raw T f).reboundary_input _ _ j j law

/-- The unchanged two-use distributor accepts exactly the two repeated actions. -/
theorem compatible : BoundarySerial.Compatible (copies T f)
    (MultiUseBoundary.ofTyped f.outputs f.output_label d 2) := by
  intro j
  obtain ⟨b,i,rfl⟩ := PairBoundary.index_surjective j
  have left := copies_output T f b i
  have right := MultiUseBoundary.ofTyped_pair_input f.outputs f.output_label d b i
  rw [BoundaryIso.map_output] at left
  rw [BoundaryIso.map_input] at right
  exact (Port.output.inj left).trans (Port.input.inj right).symm

/-- Naturality of the full literal copy reduct, including both resource distributors. -/
def after : BoundaryIso (CopyRule.after T G) (CopyRule.after T H) :=
  BoundarySerial.iso (copies T f) (MultiUseBoundary.ofTyped f.outputs f.output_label d 2) (compatible T f)

theorem after_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (after T f).ports.toFun (.input i) = .input i := by
  have h := copies_input T f i
  rw [BoundaryIso.map_input] at h
  exact (BoundarySerial.iso_input _ _ (compatible T f) i).trans (congrArg Port.input (Port.input.inj h))

theorem after_output (i : Fin (environmentInterface k h).length) :
    (after T f).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have h := MultiUseBoundary.ofTyped_output f.outputs f.output_label d 2 i
  rw [BoundaryIso.map_output] at h
  exact (BoundarySerial.iso_output _ _ (compatible T f) i).trans (congrArg Port.output (Port.output.inj h))

/-- The action maps the active payload copy to the active copy, edge by edge. -/
theorem after_leftEdge (e : G.Edge) :
    (after T f).edges.toFun (leftEdge T G e) = leftEdge T H (f.edges.toFun e) := by
  cases d <;> simp only [after,BoundarySerial.iso,BoundarySerial.edges,copies,BoundaryIso.reboundary_edges] <;> rfl

/-- The retained copy has the same payload edge action, without exchanging branches. -/
theorem after_rightEdge (e : G.Edge) :
    (after T f).edges.toFun (rightEdge T G e) = rightEdge T H (f.edges.toFun e) := by
  cases d <;> simp only [after,BoundarySerial.iso,BoundarySerial.edges,copies,BoundaryIso.reboundary_edges] <;> rfl

/-- Every residual tree and weakening edge is fixed, including its presentation. -/
theorem after_residualEdge (e : (residual T d).Edge) :
    (after T f).edges.toFun
      (Serial.leftEdge (CopyRule.copies T G) (Translation.environmentDistributor d k h 2)
        ⟨true,Serial.leftEdge (residual T d) G e⟩) =
      Serial.leftEdge (CopyRule.copies T H) (Translation.environmentDistributor d k h 2)
        ⟨true,Serial.leftEdge (residual T d) H e⟩ := by
  cases d <;> simp only [after,BoundarySerial.iso,BoundarySerial.edges,copies,BoundaryIso.reboundary_edges] <;> rfl

/-- Permuting a payload's external outputs commutes with the complete copy
construction. This is an isomorphism of reducts, not a copyability assertion. -/
def permuted (p : TypedPermutation (environmentInterface k h)) :
    DeepIso (CopyRule.after T (InterfacePermutation.net G p))
      (InterfacePermutation.net (CopyRule.after T G) p) := by
  apply DeepIso.symm
  apply InterfacePermutation.realize (after T (InterfacePermutation.iso G p)) p
  · intro i
    have h := after_input T (InterfacePermutation.iso G p) i
    rw [BoundaryIso.map_input] at h
    exact Port.input.inj h
  · intro i
    have h := after_output T (InterfacePermutation.iso G p) i
    rw [BoundaryIso.map_output] at h
    exact Port.output.inj h
end Hypernets.Copying.CopyRule.Boundary

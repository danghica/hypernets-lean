import Hypernets.Copying.BoxPullWeakeningRetainedCopy

/-! Retain both original copies and every original resource row inside the
literal copy reduct with one additional unused output. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.RetainedCopy
open Graph Opening

def targetCast {d I O J K P Q} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : Occurrence G H) (hi : J = P) (ho : K = Q) : Occurrence G (H.reboundary hi ho) where
  ports v := Port.cast hi ho (f.ports v)
  internals := f.internals
  edges := f.edges
  internal_map v := by rw [f.internal_map]; rfl
  internal_injective := f.internal_injective
  edge_injective := f.edge_injective
  internal_label := f.internal_label
  label := f.label
  source e := by
    change (G.source e).map (Port.cast hi ho ∘ f.ports) = (H.source (f.edges e)).map _
    rw [← List.map_map,f.source]
  target e := by
    change (G.target e).map (Port.cast hi ho ∘ f.ports) = (H.target (f.edges e)).map _
    rw [← List.map_map,f.target]

noncomputable def serialLeftOccurrence {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) :
    Occurrence A (Serial.net A B) :=
  (MatchEmbedding.serialLeft A B).occurrence (fun e => by cases d <;> exact labelEquiv_refl _ _)

variable {d n k h} (T : ContractionTree .term (n+1))
  (H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

noncomputable def retainedBranch :
    Occurrence (Serial.net (CopyRule.residual T d) H)
      (Serial.net (CopyRule.residual T d) (extend H s)) := by
  apply Occurrence.SerialJoin.occurrence
    (serialLeftOccurrence (CopyRule.residual T d) (extend H s))
    ((payload H s).comp (Occurrence.serialRight (CopyRule.residual T d) (extend H s)))
  · intro i
    change BoundarySerial.leftInsert _ _ (.output i) =
      BoundarySerial.rightInsert _ _ ((payload H s).ports (.input i))
    rw [payload_input,CopyRule.serial_left_output,CopyRule.serial_right_input]
  · cases d <;> intro e c eq <;> cases eq

theorem retainedBranch_output (i : Fin (environmentInterface k h).length) :
    (retainedBranch T H s).ports (.output i) = .output (outputIndex s i) := by
  unfold retainedBranch
  rw [Occurrence.SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert _ _ ((payload H s).ports (.output i)) = _
  rw [payload_output,Application.right_serial_output]

theorem retainedBranch_input (i : Fin (List.replicate n Wire.term).length) :
    (retainedBranch T H s).ports (.input i) = .input i := by
  unfold retainedBranch
  rw [Occurrence.SerialJoin.occurrence_input]
  change BoundarySerial.leftInsert _ _ (.input i) = _
  exact Combined.left_input _ _ i

def copyComponent (b : Bool) :
    Occurrence (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H) b) (CopyRule.copies T H) :=
  targetCast (Occurrence.ParallelJoin.component
    (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H)) (CopyRule.pairBoundary n k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩ b)
    (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

theorem copyOutput_eq (b : Bool) (i : Fin (environmentInterface k h).length) :
    CopyRule.copyOutput k h b i = PairBoundary.index b i := by cases b <;> rfl

noncomputable def copyComponents (b : Bool) :
    Occurrence (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H) b)
      (CopyRule.copies T (extend H s)) :=
  match b with
  | false => (payload H s).comp (copyComponent T (extend H s) false)
  | true => (retainedBranch T H s).comp (copyComponent T (extend H s) true)

theorem copyComponents_disjoint :
    ∀ a b, a ≠ b → ∀ e c, (copyComponents T H s a).edges e ≠ (copyComponents T H s b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · cases eq
  · cases eq
  · exact ne rfl

noncomputable def copies : Occurrence (CopyRule.copies T H) (CopyRule.copies T (extend H s)) :=
  (Occurrence.ParallelJoin.occurrence
    (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H)) (CopyRule.pairBoundary n k h)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (copyComponents T H s)
    (copyComponents_disjoint T H s)).reboundarySource
    (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

theorem copies_component (b : Bool)
    (v : (Net.Tensor.family H (Serial.net (CopyRule.residual T d) H) b).Vertex) :
    (copies T H s).ports (CopyRule.pairInsert T H b v) = (copyComponents T H s b).ports v := by
  unfold copies CopyRule.pairInsert
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]

theorem copies_output (b : Bool) (i : Fin (environmentInterface k h).length) :
    (copies T H s).ports (.output (PairBoundary.index b i)) =
      .output (PairBoundary.index b (outputIndex s i)) := by
  cases b
  · have law := copies_component T H s false (.output i)
    rw [CopyRule.pair_output,copyOutput_eq] at law
    change (copies T H s).ports _ =
      CopyRule.pairInsert T (extend H s) false ((payload H s).ports (.output i)) at law
    rw [payload_output,CopyRule.pair_output,copyOutput_eq] at law
    exact law
  · have law := copies_component T H s true (.output i)
    rw [CopyRule.pair_output,copyOutput_eq] at law
    change (copies T H s).ports _ =
      CopyRule.pairInsert T (extend H s) true ((retainedBranch T H s).ports (.output i)) at law
    rw [retainedBranch_output,CopyRule.pair_output,copyOutput_eq] at law
    exact law

theorem copies_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (copies T H s).ports (.input i) = .input i := by
  by_cases zero : i.val = 0
  · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
    subst i
    have law := copies_component T H s false (.input (0 : Fin 1))
    rw [CopyRule.pair_left_input] at law
    change (copies T H s).ports _ =
      CopyRule.pairInsert T (extend H s) false ((payload H s).ports (.input 0)) at law
    rw [payload_input,CopyRule.pair_left_input] at law
    exact law
  · let j : Fin (List.replicate n Wire.term).length := ⟨i.val-1,by have := i.isLt; simp at *; omega⟩
    have eq : i = ⟨j.val+1,by have := j.isLt; simp at *; omega⟩ := Fin.ext (by dsimp [j]; omega)
    have law := copies_component T H s true (.input j)
    rw [CopyRule.pair_right_input] at law
    change (copies T H s).ports _ =
      CopyRule.pairInsert T (extend H s) true ((retainedBranch T H s).ports (.input j)) at law
    rw [retainedBranch_input,CopyRule.pair_right_input] at law
    exact eq ▸ law

noncomputable def afterLeft : Occurrence (CopyRule.copies T H) (CopyRule.after T (extend H s)) :=
  (copies T H s).comp (serialLeftOccurrence _ _)

noncomputable def afterRight : Occurrence (Translation.environmentDistributor d k h 2)
    (CopyRule.after T (extend H s)) :=
  (distributor d k h s).comp (Occurrence.serialRight _ _)

theorem after_boundary (i : Fin (environmentInterface (k*2) (h*2)).length) :
    (afterLeft T H s).ports (.output i) = (afterRight T H s).ports (.input i) := by
  obtain ⟨b,j,rfl⟩ := PairBoundary.index_surjective i
  change BoundarySerial.leftInsert _ _ ((copies T H s).ports (.output _)) =
    BoundarySerial.rightInsert _ _ ((distributor d k h s).ports (.input _))
  rw [copies_output,distributor_pair_input,CopyRule.serial_left_output,CopyRule.serial_right_input]

theorem after_disjoint : ∀ e c, (afterLeft T H s).edges e ≠ (afterRight T H s).edges c := by
  cases d <;> intro e c eq <;> cases eq

/-- The complete original copy reduct retains a complete-label occurrence
inside the extended reduct. The only omitted component is the unused row. -/
noncomputable def after : Occurrence (CopyRule.after T H) (CopyRule.after T (extend H s)) :=
  Occurrence.SerialJoin.occurrence (afterLeft T H s) (afterRight T H s)
    (after_boundary T H s) (after_disjoint T H s)

theorem after_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (after T H s).ports (.input i) = .input i := by
  unfold after
  rw [Occurrence.SerialJoin.occurrence_input]
  change BoundarySerial.leftInsert _ _ ((copies T H s).ports (.input i)) = _
  rw [copies_input,Combined.left_input]

theorem after_output (i : Fin (environmentInterface k h).length) :
    (after T H s).ports (.output i) = .output (outputIndex s i) := by
  unfold after
  rw [Occurrence.SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert _ _ ((distributor d k h s).ports (.output i)) = _
  rw [distributor_output,Application.right_serial_output]


end Hypernets.Copying.BoxPullWeakening.RetainedCopy

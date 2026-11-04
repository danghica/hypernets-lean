import Hypernets.Copying.WeakeningPairOccurrences

/-! The selected binary distributor row in a pair of independent extended
operands, with its two actual incoming weakening edges. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Pair
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (serialLeftOccurrence)
variable {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) (s : ShareSort)

/-- The actual selected row in the enlarged environment distributor. -/
def row : Occurrence (CanonicalTree.atDepth s 2 d) (core (extend G s) (extend H s)) :=
  (CopyRow.selected d k h s).comp (Occurrence.serialRight _ _)

/-- One new weakening comes from each operand; the operands need not agree. -/
def weakEdge (b : Bool) : (core (extend G s) (extend H s)).Edge := by
  cases d
  all_goals
    cases b
    · exact ⟨false,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩
    · exact ⟨false,⟨true,⟨true,(0 : Fin 1)⟩⟩⟩

theorem weak_injective : Function.Injective (weakEdge G H s) := by
  cases d <;> intro a b eq <;> cases a <;> cases b <;> first | rfl | cases eq

theorem weak_disjoint (b : Bool) (e : (CanonicalTree.atDepth s 2 d).Edge) :
    weakEdge G H s b ≠ (row G H s).edges e := by
  cases d <;> cases b <;> cases s <;> intro eq <;> cases eq

theorem weak_labels (b : Bool) :
    (core (extend G s) (extend H s)).edgeLabel (weakEdge G H s b) = primitiveLabel d (.weakening s) := by
  cases d <;> cases b <;> rfl

theorem weak_sources (b : Bool) :
    (core (extend G s) (extend H s)).source (weakEdge G H s b) = [] := by
  cases d <;> cases b <;> rfl

private theorem attached_target {e I O k h} {A : Hypernet e [.term] (environmentInterface k h)}
    {B : Hypernet e I O} (s : ShareSort) (f : Occurrence (extend A s) B)
    (w : (primitiveNet e (.weakening s)).Edge) (v : B.Vertex)
    (link : f.ports (.output (CopyRow.addedOutput k h s)) = v) :
    B.target (f.edges ⟨true,w⟩) = [v] := by
  rw [← f.target,CopyRow.extended_weak_target,List.map_singleton,link]

/-- The original paired output shuffle links each weakening to its own use
of the new resource in the canonical two-input row. -/
theorem weak_target_link (b : Bool) :
    (core (extend G s) (extend H s)).target (weakEdge G H s b) =
      [.internal (.inl (PairBoundary.index b (CopyRow.addedOutput k h s)))] := by
  cases b
  · have law := attached_target s ((component (extend G s) (extend H s) false).comp (serialLeftOccurrence (paired (extend G s) (extend H s)) (Translation.environmentDistributor d (variables s k) (atoms s h) 2))) (by cases d <;> exact (0 : Fin 1)) _ (by
      change BoundarySerial.leftInsert _ _ ((component (extend G s) (extend H s) false).ports (.output _)) = _
      erw [component_output (extend G s) (extend H s) false (CopyRow.addedOutput k h s),CopyRule.serial_left_output])
    cases d <;> exact law
  · have law := attached_target s ((component (extend G s) (extend H s) true).comp (serialLeftOccurrence (paired (extend G s) (extend H s)) (Translation.environmentDistributor d (variables s k) (atoms s h) 2))) (by cases d <;> exact (0 : Fin 1)) _ (by
      change BoundarySerial.leftInsert _ _ ((component (extend G s) (extend H s) true).ports (.output _)) = _
      erw [component_output (extend G s) (extend H s) true (CopyRow.addedOutput k h s),CopyRule.serial_left_output])
    cases d <;> exact law

theorem weak_targets (b : Bool) :
    (core (extend G s) (extend H s)).target (weakEdge G H s b) =
      [(row G H s).ports (.input (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩))] := by
  rw [weak_target_link]
  change [_] = [BoundarySerial.rightInsert _ _ ((CopyRow.selected d k h s).ports _)]
  rw [CopyRow.selected_input,CopyRule.serial_right_input]
  cases b <;> rfl

/-- The complete five-edge binary weakening pattern has its actual occurrence. -/
noncomputable def unusedRow : Occurrence (IdemRow.canonical d s) (core (extend G s) (extend H s)) :=
  IdemRow.attachedOccurrence (row G H s) (weakEdge G H s) (weak_injective G H s)
    (weak_disjoint G H s) (weak_labels G H s) (weak_sources G H s) (weak_targets G H s)

theorem unusedRow_output (i : Fin 1) :
    (unusedRow G H s).ports (.output i) = .output (CopyRow.addedOutput k h s) := by
  have zero : i = 0 := Subsingleton.elim _ _
  subst i
  cases d
  all_goals
    change (row G H s).ports (.output 0) = _
    simp only [row,Occurrence.comp,Occurrence.serialRight,Function.comp_apply]
    cases s <;> simp only [CopyRow.selected,CopyRow.termOccurrence,CopyRow.atomOccurrence,CopyRow.forestOccurrence,Net.Parallel.embed]
    all_goals
      rw [Application.right_serial_output]
      apply congrArg Port.output
      apply Fin.ext
      simp [CopyRow.addedOutput,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,Distributor.boundary,List.length_replicate]

end Hypernets.Copying.Weakening.Pair

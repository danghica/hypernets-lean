import Hypernets.Copying.BoxPullWeakeningReverseCopyable
import Hypernets.Copying.TwoInputContractionSubtree
import Hypernets.Copying.EqualityTreeRematch
import Hypernets.Copying.ReadTreeRematch
import Hypernets.Copying.AssignmentTreeRematch

/-! Nonweak primitive footprints for converse BPullW matching. Unused atom
siblings are removed only from the selected local match, never from the host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.ReverseComponents
open Graph Opening

abbrev Nonweak {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e, ∃ p, G.edgeLabel e = primitiveLabel d p ∧ ∀ s, p ≠ .weakening s

theorem serial_nonweak {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (left : Nonweak G) (right : Nonweak H) : Nonweak (Serial.net G H) := by
  cases d <;> rintro ⟨b,e⟩ <;> cases b <;> first | exact left e | exact right e

theorem tensor_nonweak {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (left : Nonweak G) (right : Nonweak H) : Nonweak (Net.Tensor.net G H) := by
  rintro ⟨b,e⟩; cases b
  · exact left e
  · exact right e

theorem allocation_nonweak {d J} (G : Hypernet d [.term] J) (stable : Stable G) :
    Nonweak (Allocation.before G) :=
  serial_nonweak (primitive_nonweak d _ (fun _ eq => by cases eq)) (stable_nonweak stable)

theorem unary_nonweak (d n : Nat) : Nonweak (Arithmetic.unaryBefore d n) :=
  serial_nonweak (primitive_nonweak d _ (fun _ eq => by cases eq))
    (primitive_nonweak d _ (fun _ eq => by cases eq))

theorem binary_nonweak (o : Arithmetic.BinaryCode) (d m n : Nat) :
    Nonweak (Arithmetic.binaryBefore o d m n) :=
  serial_nonweak (primitive_nonweak d _ (fun _ eq => by cases eq))
    (tensor_nonweak (primitive_nonweak d _ (fun _ eq => by cases eq))
      (primitive_nonweak d _ (fun _ eq => by cases eq)))

theorem read_nonweak {h} (T : ContractionTree .atom (h+1))
    (tree : ∀ e, T.net.edgeLabel e = .contraction .atom) (d : Nat) :
    Nonweak (Dereference.before T d) := by
  rintro ⟨part,e⟩
  cases part
  · exact ⟨_,rfl,fun _ eq => by cases eq⟩
  · exact ⟨_,rfl,fun _ eq => by cases eq⟩
  · exact ⟨.contraction .atom,congrArg (primitiveLabel d) (tree e),fun _ eq => by cases eq⟩
  · exact ⟨_,rfl,fun _ eq => by cases eq⟩

theorem assignment_nonweak {d h J} (T : ContractionTree .atom (h+1))
    (tree : ∀ e, T.net.edgeLabel e = .contraction .atom)
    (G : Hypernet d [.term] J) (stable : Stable G) : Nonweak (Assignment.before T G) := by
  cases d <;> rintro ⟨part,e⟩ <;> cases part
  all_goals first
    | exact stable_nonweak stable e
    | exact ⟨.contraction .atom,(Assignment.tree_labels T G e).1.trans (congrArg (primitiveLabel _) (tree e)),fun _ eq => by cases eq⟩
    | exact ⟨_,rfl,fun _ eq => by cases eq⟩

theorem same_nonweak {h} (T : ContractionTree .atom (h+2))
    (tree : ∀ e, T.net.edgeLabel e = .contraction .atom) (d : Nat) :
    Nonweak (AtomEquality.Same.before T d) := by
  rintro ⟨part,e⟩
  cases part
  all_goals first
    | exact ⟨.contraction .atom,congrArg (primitiveLabel d) (tree e),fun _ eq => by cases eq⟩
    | exact ⟨_,rfl,fun _ eq => by cases eq⟩

theorem different_nonweak {m n} (T : ContractionTree .atom (m+1)) (U : ContractionTree .atom (n+1))
    (left : ∀ e, T.net.edgeLabel e = .contraction .atom)
    (right : ∀ e, U.net.edgeLabel e = .contraction .atom) (d : Nat) :
    Nonweak (AtomEquality.Different.before T U d) := by
  rintro ⟨part,e⟩
  cases part
  all_goals first
    | exact ⟨.contraction .atom,congrArg (primitiveLabel d) (left e),fun _ eq => by cases eq⟩
    | exact ⟨.contraction .atom,congrArg (primitiveLabel d) (right e),fun _ eq => by cases eq⟩
    | exact ⟨_,rfl,fun _ eq => by cases eq⟩

/-- Every edge on a directed path from an actual input is a contraction. -/
theorem fromInput_contraction {s m} (T : ContractionTree s m)
    {i e} (path : T.FromInput i e) : T.net.edgeLabel e = .contraction s := by
  obtain ⟨a,n,entry,path⟩ := path
  have sourced : ∃ v, v ∈ T.net.source e := by
    have start : ∃ v, v ∈ T.net.source a := ⟨_,entry⟩
    clear entry
    induction path with
    | refl _ => exact start
    | step adj path ih => exact ih (by obtain ⟨v,_,h⟩ := adj; exact ⟨v,h⟩)
  rcases T.labels e with weak | contraction
  · obtain ⟨v,hv⟩ := sourced
    have zero := T.net.source_length e
    rw [weak] at zero
    change (T.net.source e).length = 0 at zero
    exact False.elim (List.not_mem_nil (List.eq_nil_of_length_eq_zero zero ▸ hv))
  · exact contraction

/-- The two-input selected subtree has no weakening edge, even when the
original full tree contains arbitrary unused weakening branches. -/
theorem selected_nonweak {d s m n} (T : ContractionTree s m) (U : ContractionTree s n)
    (f : Occurrence (U.atDepth d) (T.atDepth d)) {i j}
    (paths : ∀ e, T.FromInput i (f.edges e) ∨ T.FromInput j (f.edges e)) :
    ∀ e, U.net.edgeLabel e = .contraction s := by
  intro e
  have original : T.net.edgeLabel (f.edges e) = .contraction s := by
    rcases paths e with h | h <;> exact fromInput_contraction T h
  rcases U.labels e with weak | contraction
  · have moved := f.matchEmbedding.primitive e (.weakening s) (congrArg (primitiveLabel d) weak)
    change primitiveLabel d (T.net.edgeLabel (f.edges e)) = primitiveLabel d (.weakening s) at moved
    rw [original] at moved
    cases primitiveLabel_injective d moved
  · exact contraction
end Hypernets.Copying.BoxPullWeakening.ReverseComponents

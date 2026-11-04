import Hypernets.Copying.SelectedResourceRenaming
import Hypernets.Copying.OccurrenceInterfaceTransport

/-! Injective resource maps on the actual selected-resource graph. The selected
contraction and its own weakening are retained, not replaced by an ideal wire. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SelectedResource
open Graph Opening

def mapOutput {n m} (ρ : Fin n → Fin m) : Port Unit 1 n → Port Unit 1 m
  | .internal v => .internal v
  | .input i => .input i
  | .output j => .output (ρ j)

theorem source_map {n m} (ρ : Fin n → Fin m) (x : Fin n ⊕ Unit) :
    (source x).map (mapOutput ρ) = source (Sum.map ρ id x) := by cases x <;> rfl

theorem target_map {n m} (ρ : Fin n → Fin m) (inj : Function.Injective ρ)
    (i : Fin n) (x : Fin n ⊕ Unit) :
    (target i x).map (mapOutput ρ) = target (ρ i) (Sum.map ρ id x) := by
  cases x with
  | inr u => rfl
  | inl j =>
    have eq : ρ j = ρ i ↔ j = i := ⟨fun eq => inj eq,congrArg ρ⟩
    simp only [target,Sum.map_inl,eq,List.map_singleton]
    split <;> rfl

/-- A complete-label occurrence for every injective resource map, including
proper extensions of the environment. -/
def rawEmbedding (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) (i : Fin n) :
    Occurrence (raw s d i) (raw s d (ρ i)) where
  ports v := (ports s d (ρ i)).invFun (mapOutput ρ ((ports s d i).toFun v))
  internals v := (internal s d (ρ i)).invFun ((internal s d i).toFun v)
  edges e := edgeAt s d (ρ i) (Sum.map ρ id (edgeIndex s d i e))
  internal_map _ := rfl
  internal_injective := fun _ _ eq => (internal s d i).injective ((internal s d (ρ i)).symm.injective eq)
  edge_injective := by
    intro a b eq
    apply (edges s d i).injective
    change edgeIndex s d i a = edgeIndex s d i b
    have h := (edges s d (ρ i)).symm.injective eq
    cases ha : edgeIndex s d i a <;> cases hb : edgeIndex s d i b
    all_goals simp only [ha,hb,Sum.map_inl,Sum.map_inr,id_eq] at h
    · exact congrArg Sum.inl (inj (Sum.inl.inj h))
    · cases h
    · cases h
    · rfl
  internal_label v := (vertex_label s d (ρ i) (.internal _)).trans (vertex_label s d i (.internal v)).symm
  label e := by
    have law := label_at s d i (edgeIndex s d i e)
    rw [edgeAt_index] at law
    rw [law,label_at]
    cases edgeIndex s d i e <;> exact labelEquiv_refl _ _
  source e := by
    have law := source_eq s d i (edgeIndex s d i e)
    rw [edgeAt_index] at law
    rw [law,source_eq,← source_map ρ]
    simp only [List.map_map,Function.comp_def,(ports s d i).right_inv]
  target e := by
    have law := target_eq s d i (edgeIndex s d i e)
    rw [edgeAt_index] at law
    rw [law,target_eq,← target_map ρ inj]
    simp only [List.map_map,Function.comp_def,(ports s d i).right_inv]

theorem input_interface (s : ShareSort) {n} (i : Fin n) :
    (List.replicate (i.val*0) s.wire ++ List.replicate (1*1) s.wire) ++
      List.replicate ((n-i.val-1)*0) s.wire = [s.wire] := by simp

theorem output_interface (s : ShareSort) {n} (i : Fin n) :
    (List.replicate i.val s.wire ++ List.replicate 1 s.wire) ++
      List.replicate (n-i.val-1) s.wire = List.replicate n s.wire := by
  rw [List.replicate_append_replicate,List.replicate_append_replicate]
  congr 1
  have := i.isLt
  omega

/-- The original Figure 16 clause, with its equal-interface transports. -/
def embedding (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) (i : Fin n) :
    Occurrence (Translation.selectedResource d s i) (Translation.selectedResource d s (ρ i)) := by
  unfold Translation.selectedResource
  exact (rawEmbedding s d ρ inj i).castInterfaces _ _ _ _

theorem embedding_input (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) (i : Fin n)
    (j : Fin [s.wire].length) : (embedding s d ρ inj i).ports (.input j) = .input j := by
  exact (rawEmbedding s d ρ inj i).castInterfaces_input
    (U := [s.wire]) (V := List.replicate n s.wire) (W := [s.wire]) (X := List.replicate m s.wire)
    (input_interface s i) (output_interface s i) (input_interface s (ρ i)) (output_interface s (ρ i))
    ⟨j.val,by rw [input_length]; exact j.isLt⟩
    ⟨j.val,by rw [input_length]; exact j.isLt⟩ rfl

theorem embedding_output (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) (i j : Fin n) :
    (embedding s d ρ inj i).ports (.output ⟨j.val,by simp⟩) =
      .output ⟨(ρ j).val,by simp⟩ := by
  exact (rawEmbedding s d ρ inj i).castInterfaces_output
    (U := [s.wire]) (V := List.replicate n s.wire) (W := [s.wire]) (X := List.replicate m s.wire)
    (input_interface s i) (output_interface s i) (input_interface s (ρ i)) (output_interface s (ρ i))
    ⟨j.val,by rw [output_length]; exact j.isLt⟩
    ⟨(ρ j).val,by rw [output_length]; exact (ρ j).isLt⟩ rfl

end Hypernets.Copying.SelectedResource

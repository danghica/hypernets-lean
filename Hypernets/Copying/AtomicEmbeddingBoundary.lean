import Hypernets.Copying.AtomicResourceEmbedding

/-! Ordered boundary actions of the original atomic resource embeddings. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening EnvironmentPermutation
variable {d k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j)
  (rinj : Function.Injective ρ) (ainj : Function.Injective α)

theorem variable_input (i : Fin k) (v : Fin 1) :
    (variableMap (d := d) ρ α rinj ainj i).ports (.input v) = .input v := by
  let f := SelectedResource.embedding .term d ρ rinj i
  let g := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_input_left f g v v (SelectedResource.embedding_input _ _ _ _ _ v)
  exact (f.tensorMap g).castInterfaces_input (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [ShareSort.wire]) rfl
    (by simp [ShareSort.wire]) rfl _ _ law

theorem variable_term (i x : Fin k) :
    (variableMap (d := d) ρ α rinj ainj i).ports (.output (termIndex x)) = .output (termIndex (ρ x)) := by
  let f := SelectedResource.embedding .term d ρ rinj i
  let g := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_output_left f g _ _ (SelectedResource.embedding_output _ _ _ _ i x)
  exact (f.tensorMap g).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [ShareSort.wire]) rfl
    (by simp [ShareSort.wire]) rfl _ _ law

theorem variable_atom (i : Fin k) (a : Fin h) :
    (variableMap (d := d) ρ α rinj ainj i).ports (.output (atomIndex a)) = .output (atomIndex (α a)) := by
  let f := SelectedResource.embedding .term d ρ rinj i
  let g := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_output_right f g _ _ (forestEmbedding_output .atom d α ainj a)
  have mapped :=
    (f.tensorMap g).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [ShareSort.wire]) rfl
      (by simp [ShareSort.wire]) rfl _ _ law
  simp only [Net.Tensor.join,List.length_replicate,Fin.cast,EnvironmentPermutation.atomIndex] at mapped
  exact mapped

theorem atom_input (a : Fin h) (v : Fin 1) :
    (atom (d := d) ρ α rinj ainj a).ports (.input v) = .input v := by
  let f := forestEmbedding .term d ρ rinj
  let q := SelectedResource.embedding .atom d α ainj a
  let g := q.serialPrefix (primitiveNet d .instanceEdge) (SelectedResource.embedding_input _ _ _ _ a)
  have law := Occurrence.tensorMap_input_right f g _ _
    (Occurrence.serialPrefix_input (primitiveNet d .instanceEdge) q (SelectedResource.embedding_input _ _ _ _ a) v)
  have mapped := (f.tensorMap g).castInterfaces_input (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature]) rfl
    (by simp [primitiveSignature]) rfl _ _ law
  simp only [Net.Tensor.join,List.length_replicate,Nat.mul_zero,Nat.zero_add,Fin.cast] at mapped
  exact mapped

theorem atom_term (a : Fin h) (x : Fin k) :
    (atom (d := d) ρ α rinj ainj a).ports (.output (termIndex x)) = .output (termIndex (ρ x)) := by
  let f := forestEmbedding .term d ρ rinj
  let q := SelectedResource.embedding .atom d α ainj a
  let g := q.serialPrefix (primitiveNet d .instanceEdge) (SelectedResource.embedding_input _ _ _ _ a)
  have law := Occurrence.tensorMap_output_left f g _ _ (forestEmbedding_output .term d ρ rinj x)
  exact (f.tensorMap g).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature]) rfl
    (by simp [primitiveSignature]) rfl _ _ law

theorem atom_atom (a x : Fin h) :
    (atom (d := d) ρ α rinj ainj a).ports (.output (atomIndex x)) = .output (atomIndex (α x)) := by
  let f := forestEmbedding .term d ρ rinj
  let q := SelectedResource.embedding .atom d α ainj a
  let g := q.serialPrefix (primitiveNet d .instanceEdge) (SelectedResource.embedding_input _ _ _ _ a)
  have law := Occurrence.tensorMap_output_right f g _ _
    (Occurrence.serialPrefix_output _ q (SelectedResource.embedding_input _ _ _ _ a) _ _
      (SelectedResource.embedding_output .atom d α ainj a x))
  have mapped :=
    (f.tensorMap g).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature]) rfl
      (by simp [primitiveSignature]) rfl _ _ law
  simp only [Net.Tensor.join,List.length_replicate,Fin.cast,EnvironmentPermutation.atomIndex] at mapped
  exact mapped

theorem constant_input (c : Constant) (v : Fin 1) :
    (constant (d := d) ρ α rinj ainj c).ports (.input v) = .input v := by
  let f := forestEmbedding .term d ρ rinj
  let g := Occurrence.ofIso (DeepIso.refl (primitiveNet d (.operation (.const c))))
  let q := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_input_left (f.tensorMap g) q _ _
    (Occurrence.tensorMap_input_right f g v v rfl)
  have mapped :=
    ((f.tensorMap g).tensorMap q).castInterfaces_input (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature])
    (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire])
    (by simp [primitiveSignature])
    (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire]) _ _ law
  simp only [Net.Tensor.join,List.length_replicate,Nat.mul_zero,Nat.zero_add,Fin.cast] at mapped
  exact mapped

theorem constant_term (c : Constant) (x : Fin k) :
    (constant (d := d) ρ α rinj ainj c).ports (.output (termIndex x)) = .output (termIndex (ρ x)) := by
  let f := forestEmbedding .term d ρ rinj
  let g := Occurrence.ofIso (DeepIso.refl (primitiveNet d (.operation (.const c))))
  let q := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_output_left (f.tensorMap g) q _ _
    (Occurrence.tensorMap_output_left f g _ _ (forestEmbedding_output .term d ρ rinj x))
  exact ((f.tensorMap g).tensorMap q).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature])
    (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire])
    (by simp [primitiveSignature])
    (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire]) _ _ law

theorem constant_atom (c : Constant) (a : Fin h) :
    (constant (d := d) ρ α rinj ainj c).ports (.output (atomIndex a)) = .output (atomIndex (α a)) := by
  let f := forestEmbedding .term d ρ rinj
  let g := Occurrence.ofIso (DeepIso.refl (primitiveNet d (.operation (.const c))))
  let q := forestEmbedding .atom d α ainj
  have law := Occurrence.tensorMap_output_right (f.tensorMap g) q _ _ (forestEmbedding_output .atom d α ainj a)
  have mapped :=
    ((f.tensorMap g).tensorMap q).castInterfaces_output (U := [.term]) (V := environmentInterface k h)
    (W := [.term]) (X := environmentInterface l j) (by simp [primitiveSignature])
      (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire])
      (by simp [primitiveSignature])
      (by simp [environmentInterface,primitiveSignature,Operation.outputs,ShareSort.wire]) _ _ law
  simp only [Net.Tensor.join,List.length_append,List.length_replicate,List.length_nil,Nat.add_zero,Fin.cast,EnvironmentPermutation.atomIndex,primitiveSignature,Operation.outputs] at mapped
  exact mapped

end Hypernets.Copying.Weakening.Atomic

import Hypernets.Copying.WeakeningRowPartition

/-! Reconstructing an original graph with one independent unused resource from
an exhaustive occurrence partition. No operational or equivalence premise. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Extension
open Graph Opening BoxPullWeakening
open BoxPullWeakening.RetainedCopy (payload outputIndex payload_input)

structure Witness {d I k h} (s : ShareSort) (G : Hypernet d I (environmentInterface k h))
    (H : Hypernet d I (environmentInterface (variables s k) (atoms s h))) where
  old : Occurrence G H
  added : Occurrence (primitiveNet d (.weakening s)) H
  disjoint : ∀ e a, old.edges e ≠ added.edges a
  cover : ∀ e, (∃ a, old.edges a = e) ∨ ∃ b, added.edges b = e
  input : ∀ i, old.ports (.input i) = .input i
  output : ∀ i, old.ports (.output i) = .output (outputIndex s i)
  new_output : ∀ i, added.ports (.output i) = .output (CopyRow.addedOutput k h s)

variable {d I k h s} {G : Hypernet d I (environmentInterface k h)}
  {H : Hypernet d I (environmentInterface (variables s k) (atoms s h))} (q : Witness s G H)

def components (b : Bool) : Occurrence (Net.Tensor.family G (primitiveNet d (.weakening s)) b) H :=
  match b with | false => q.old | true => q.added

theorem disjoint : ∀ a b, a ≠ b → ∀ e c, (components q a).edges e ≠ (components q b).edges c := by
  intro a b ne e c eq
  cases a <;> cases b
  · exact ne rfl
  · exact q.disjoint e c eq
  · exact q.disjoint c e eq.symm
  · exact ne rfl

noncomputable def occurrence : Occurrence (extend G s) H :=
  (Occurrence.ParallelJoin.occurrence _ (insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s)
    ⟨[false,true],by intro b; cases b <;> simp⟩ (components q) (disjoint q)).reboundarySource
      (List.append_nil I) (extended_interface s k h)

theorem old_port (v : G.Vertex) : (occurrence q).ports ((payload G s).ports v) = q.old.ports v := by
  unfold occurrence payload
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]
  rfl

theorem input (i : Fin I.length) : (occurrence q).ports (.input i) = .input i := by
  rw [← payload_input G s i,old_port,q.input]

theorem component_output (b : Bool)
    (i : Fin (Net.Tensor.interfaces (environmentInterface k h) [s.wire] b).length) :
    (components q b).ports (.output i) =
      .output (Fin.cast (congrArg List.length (extended_interface s k h))
        ((insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s).outputs.toFun ⟨b,i⟩)) := by
  cases b
  · change q.old.ports (.output i) = _
    rw [q.output]
    exact congrArg Port.output (Fin.ext (inserted_old_output (I := I) s i).symm)
  · change q.added.ports (.output i) = _
    rw [q.new_output]
    have zero : i = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
    subst i
    apply congrArg Port.output
    apply Fin.ext
    change k = _
    simpa only [Fin.val_cast,List.length_replicate] using
      (inserted_weakening_output (I := I) (A := List.replicate k .term) (B := List.replicate h .atom) s).symm

theorem output (i : Fin (environmentInterface (variables s k) (atoms s h)).length) :
    (occurrence q).ports (.output i) = .output i := by
  let B := insertionBoundary I (List.replicate k .term) (List.replicate h .atom) s
  let j := Fin.cast (congrArg List.length (extended_interface s k h).symm) i
  change (components q (B.outputs.invFun j).1).ports (.output (B.outputs.invFun j).2) = _
  rw [component_output]
  change Port.output (Fin.cast _ (B.outputs.toFun (B.outputs.invFun j))) = _
  rw [B.outputs.right_inv]
  rfl

theorem edge_surjective : Function.Surjective (occurrence q).edges := by
  intro e
  rcases q.cover e with ⟨a,eq⟩ | ⟨b,eq⟩
  · exact ⟨⟨false,a⟩,eq⟩
  · exact ⟨⟨true,b⟩,eq⟩

noncomputable def iso : DeepIso (extend G s) H :=
  (occurrence q).iso_of_edge_surjective (input q) (output q) (edge_surjective q)

end Hypernets.Copying.Weakening.Extension

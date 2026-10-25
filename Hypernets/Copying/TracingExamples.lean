import Hypernets.Copying.ContractionTree
import Hypernets.Copying.StoreTrace
import Hypernets.Graph.PathRank

namespace Hypernets.Copying.Examples
open Graph

/-- A contraction tree without any weakening: two exposed leaves and one root. -/
def binaryTree (s : ShareSort) : ContractionTree s 2 where
  net := Net.corolla primitiveSignature (.contraction s)
  labels _ := .inr rfl
  acyclic := by
    apply Net.path_nodup_of_rank _ (fun _ => 0)
    intro e f ⟨v,ht,hs⟩
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp ht
    obtain ⟨j,_,eq⟩ := List.mem_map.mp hs
    cases eq

/-- Arbitrary-tree termination includes the weakening-free binary tree. -/
theorem binaryTree_reaches (s : ShareSort) (e : (binaryTree s).net.Edge) :
    ∃ n, Trace (binaryTree s).net.Adjacent e (binaryTree s).root n :=
  (binaryTree s).reaches_root e

/-- A store containing its own instance: a genuine directed two-edge cycle. -/
@[reducible] def cyclicStore (d : Nat) : Hypernet d [] [] where
  Internal := Bool
  Edge := Bool
  finiteInternal := ⟨[false,true],by intro b; cases b <;> simp⟩
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel b := if b then .atom else .term
  edgeLabel b := primitiveLabel d (if b then .store else .instanceEdge)
  source b := [.internal b]
  target b := [.internal (!b)]
  source_nodup _ := by simp
  target_nodup _ := by simp
  source_unique := by intro v e f he hf; simp at he hf; exact Port.internal.inj (he.symm.trans hf)
  target_unique := by
    intro v e f he hf
    simp only [List.mem_singleton] at he hf
    have eq := Port.internal.inj (he.symm.trans hf)
    cases e <;> cases f <;> simp_all
  source_coverage := by
    intro v
    cases v with
    | internal b => simp [Port.IsOutput]
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  target_coverage := by
    intro v
    cases v with
    | internal b =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _; exact ⟨!b,by simp⟩
    | input i => exact Fin.elim0 i
    | output i => exact Fin.elim0 i
  source_typed b := by cases b <;> simp [Port.label, primitive_input, primitiveSignature]
  target_typed b := by cases b <;> simp [Port.label, primitive_output, primitiveSignature]

/-- The ambient graph really has a cyclic path; global acyclicity is unavailable. -/
theorem cyclicStore_cycle (d : Nat) : (cyclicStore d).Path [false,true,false] := by
  apply Net.Path.cons (show (cyclicStore d).Adjacent false true from ⟨.internal true,by simp [cyclicStore],by simp [cyclicStore]⟩)
  apply Net.Path.cons (show (cyclicStore d).Adjacent true false from ⟨.internal false,by simp [cyclicStore],by simp [cyclicStore]⟩)
  exact .single _

/-- Atom resolution stops at the store even though its stored value closes a cycle. -/
theorem cyclicStore_resolves (d : Nat) : StoreTrace.Resolves (cyclicStore d) false true 1 := by
  refine ⟨.step ?_ (.refl true),rfl⟩
  exact ⟨.inl rfl,⟨.internal true,by simp [cyclicStore],by simp [cyclicStore]⟩⟩

/-- Every successful resolution of this instance uses the same store and one hop. -/
theorem cyclicStore_unique (d : Nat) (e : (cyclicStore d).Edge) (n : Nat)
    (h : StoreTrace.Resolves (cyclicStore d) false e n) : e = true ∧ n = 1 :=
  StoreTrace.resolves_unique h (cyclicStore_resolves d)

/-- The cycle is compatible with the graph being globally hole-free. -/
theorem cyclicStore_holeFree (d : Nat) : HoleFree (cyclicStore d) := by
  intro b
  cases d <;> cases b <;> intro hole eq <;> cases eq

end Hypernets.Copying.Examples

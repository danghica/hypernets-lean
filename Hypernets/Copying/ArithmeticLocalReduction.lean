import Hypernets.Copying.ArithmeticReductionExpansion

/-! The original arithmetic rules supply complete deletion certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph

theorem fin_two (i : Fin 2) : i = 0 ∨ i = 1 := by omega

theorem unary_internal_deleted (d n : Nat) (x : (unaryBefore d n).Internal) :
    Port.internal x ∈ (unaryBefore d n).target (unaryHead d n) := by
  cases d <;> rcases x with i | ⟨b,x⟩
  all_goals first
    | (cases DiscardResult.fin_one i; exact List.mem_cons_self)
    | (cases b <;> exact nomatch x)

theorem binary_internal_deleted (o : BinaryCode) (d m n : Nat) (x : (binaryBefore o d m n).Internal) :
    Port.internal x ∈ (binaryBefore o d m n).target (binaryHead o d m n) := by
  cases d <;> rcases x with i | ⟨b,x⟩
  all_goals first
    | (rcases fin_two i with rfl | rfl
       · exact List.mem_cons_self
       · exact List.mem_cons_of_mem _ List.mem_cons_self)
    | (cases b with
       | false => exact nomatch x
       | true => rcases x with ⟨c,x⟩; cases c <;> exact nomatch x)

theorem unary_internal_targets (d n : Nat) : InternalTargets (unaryBefore d n) (unaryHead d n) := by
  cases d <;> intro v hv <;> change v ∈ [Port.internal (.inl (0 : Fin 1))] at hv
  all_goals cases List.mem_singleton.mp hv; exact ⟨_,rfl⟩

theorem binary_internal_targets (o : BinaryCode) (d m n : Nat) :
    InternalTargets (binaryBefore o d m n) (binaryHead o d m n) := by
  cases d <;> intro v hv <;> change v ∈ [Port.internal (.inl (0 : Fin 2)),Port.internal (.inl (1 : Fin 2))] at hv
  all_goals simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  all_goals rcases hv with rfl | rfl <;> exact ⟨_,rfl⟩

theorem unary_adjacent_iff (d n : Nat) (e : (unaryBefore d n).Edge) :
    (unaryBefore d n).Adjacent (unaryHead d n) e ↔ e ≠ unaryHead d n := by
  cases d <;> rcases e with ⟨b,i⟩ <;> cases b <;> cases DiscardResult.fin_one i
  all_goals
    first
    | (change (∃ v : (unaryBefore _ n).Vertex, v ∈ [Port.internal (.inl (0 : Fin 1))] ∧ v ∈ [Port.input 0]) ↔ _
       simp)
    | (change (∃ v : (unaryBefore _ n).Vertex, v ∈ [Port.internal (.inl (0 : Fin 1))] ∧ v ∈ [Port.internal (.inl (0 : Fin 1))]) ↔ _
       simp [unaryHead])

  all_goals first | rfl | (intro eq; cases congrArg Sigma.fst eq)

theorem binary_adjacent_iff (o : BinaryCode) (d m n : Nat) (e : (binaryBefore o d m n).Edge) :
    (binaryBefore o d m n).Adjacent (binaryHead o d m n) e ↔ e ≠ binaryHead o d m n := by
  cases d <;> rcases e with ⟨b,e⟩ <;> cases b
  all_goals first
    | (cases DiscardResult.fin_one e
       change (∃ v : (binaryBefore o _ m n).Vertex,
         v ∈ [Port.internal (.inl (0 : Fin 2)),Port.internal (.inl (1 : Fin 2))] ∧ v ∈ [Port.input 0]) ↔ _
       simp)
    | (rcases e with ⟨c,e⟩; cases c <;> cases DiscardResult.fin_one e
       all_goals
         first
         | (change (∃ v : (binaryBefore o _ m n).Vertex,
              v ∈ [Port.internal (.inl (0 : Fin 2)),Port.internal (.inl (1 : Fin 2))] ∧ v ∈ [Port.internal (.inl (0 : Fin 2))]) ↔ _
            simp [binaryHead])
         | (change (∃ v : (binaryBefore o _ m n).Vertex,
              v ∈ [Port.internal (.inl (0 : Fin 2)),Port.internal (.inl (1 : Fin 2))] ∧ v ∈ [Port.internal (.inl (1 : Fin 2))]) ↔ _
            simp [binaryHead]))

  all_goals first | rfl | (intro eq; cases congrArg Sigma.fst eq)

/-- A closed numeric redex with no surviving internal wires reduces to its result corolla. -/
def result_reduction {d} (G : Hypernet d [.term] []) (head : G.Edge) (result : Nat)
    (deleted : ∀ x, Port.internal x ∈ G.target head)
    (adj : ∀ e, G.Adjacent head e ↔ e ≠ head)
    (src : G.source head = [.input 0]) : Reduction G (number d result) head result := by
  classical
  cases d <;> refine {
    vertices := fun x => nomatch x
    vertex_injective := fun x => nomatch x
    vertex_range := by
      intro x
      constructor
      · rintro ⟨y,_⟩; exact nomatch y
      · intro h; exact False.elim (h (deleted x))
    edges := fun _ => head
    edge_injective := fun x y _ => by cases DiscardResult.fin_one x; cases DiscardResult.fin_one y; rfl
    edge_range := by
      intro e
      rw [adj]
      exact ⟨fun ⟨_,eq⟩ ne => ne eq.symm,fun h => ⟨(0 : Fin 1),(Classical.byContradiction h).symm⟩⟩
    internal_label := fun x => nomatch x
    edge_head := fun _ _ => rfl
    edge_other := fun _ ne => False.elim (ne rfl)
    source := by
      intro e
      cases DiscardResult.fin_one e
      exact src.symm
    target_head := fun _ _ => rfl
    target_other := fun _ ne => False.elim (ne rfl) }

def unary_reduction (d n : Nat) :
    Reduction (unaryBefore d n) (unaryAfter d n) (unaryHead d n) (neg n) :=
  result_reduction _ _ _ (unary_internal_deleted d n) (unary_adjacent_iff d n) (by cases d <;> rfl)

def binary_reduction (o : BinaryCode) (d m n : Nat) :
    Reduction (binaryBefore o d m n) (binaryAfter o d m n) (binaryHead o d m n) (o.eval m n) :=
  result_reduction _ _ _ (binary_internal_deleted o d m n) (binary_adjacent_iff o d m n) (by cases d <;> rfl)
end Hypernets.Copying.Arithmetic

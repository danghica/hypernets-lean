import Hypernets.Copying.StoreMatching

/-! Ordered numeric operands are intrinsic to a redex in its host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph MatchEmbedding

/-- The ith argument is an actual natural-number edge. -/
def NumberArgument {d I O} (G : Hypernet d I O) (e : G.Edge) (i n : Nat) : Prop :=
  ∃ a, Argument G e i a ∧ G.edgeLabel a = primitiveLabel d (.operation (.const (.nat n)))

theorem numberArgument_unique {d I O} {G : Hypernet d I O} {e i m n}
    (hm : NumberArgument G e i m) (hn : NumberArgument G e i n) : m = n := by
  obtain ⟨a,ha,la⟩ := hm
  obtain ⟨b,hb,lb⟩ := hn
  have eq := argument_unique ha hb
  subst b
  have eq := primitiveLabel_injective d (la.symm.trans lb)
  cases eq; rfl

theorem numberArgument_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {e i n} (h : NumberArgument G e i n) : NumberArgument H (f.edges e) i n := by
  obtain ⟨a,arg,label⟩ := h
  exact ⟨f.edges a,f.argument arg,f.primitive _ _ label⟩

theorem unary_head (d n : Nat) : HeadAt (unaryBefore d n) (.input 0) (unaryHead d n) (.operation (.unary .neg)) := by
  cases d <;> exact ⟨rfl,List.mem_cons_self⟩

theorem unary_operand (d n : Nat) : NumberArgument (unaryBefore d n) (unaryHead d n) 0 n := by
  refine ⟨unaryValue d n,⟨unaryArgument d n,?_,?_⟩,?_⟩
  · cases d <;> rfl
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

theorem binary_head (o : BinaryCode) (d m n : Nat) :
    HeadAt (binaryBefore o d m n) (.input 0) (binaryHead o d m n) (.operation (.binary o.symbol)) := by
  cases d <;> exact ⟨rfl,List.mem_cons_self⟩

theorem binary_left_operand (o : BinaryCode) (d m n : Nat) :
    NumberArgument (binaryBefore o d m n) (binaryHead o d m n) 0 m := by
  refine ⟨binaryValue o d m n false,⟨binaryArgument o d m n 0,?_,?_⟩,?_⟩
  · cases d <;> rfl
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

theorem binary_right_operand (o : BinaryCode) (d m n : Nat) :
    NumberArgument (binaryBefore o d m n) (binaryHead o d m n) 1 n := by
  refine ⟨binaryValue o d m n true,⟨binaryArgument o d m n 1,?_,?_⟩,?_⟩
  · cases d <;> rfl
  · cases d <;> exact List.mem_cons_self
  · cases d <;> rfl

theorem BinaryCode.symbol_injective {o p : BinaryCode} (h : o.symbol = p.symbol) : o = p := by
  cases o <;> cases p <;> simp_all [symbol]

/-- Independently embedded binary redexes agree on operation and both ordered operands. -/
theorem binary_match_unique {d r s I O} {G : Hypernet d I O} {o p m n a b}
    (f : MatchEmbedding (binaryBefore o r m n) G) (g : MatchEmbedding (binaryBefore p s a b) G)
    (same : f.ports (.input 0) = g.ports (.input 0)) : o = p ∧ m = a ∧ n = b := by
  have hf := f.head (binary_head o r m n)
  have hg := g.head (binary_head p s a b)
  rw [same] at hf
  obtain ⟨edge,label⟩ := head_unique hf hg
  have codes : o = p := BinaryCode.symbol_injective (Operation.binary.inj (Primitive.operation.inj label))
  refine ⟨codes,?_,?_⟩
  · exact numberArgument_unique (edge ▸ numberArgument_map f (binary_left_operand o r m n))
      (numberArgument_map g (binary_left_operand p s a b))
  · exact numberArgument_unique (edge ▸ numberArgument_map f (binary_right_operand o r m n))
      (numberArgument_map g (binary_right_operand p s a b))
end Hypernets.Copying.Arithmetic

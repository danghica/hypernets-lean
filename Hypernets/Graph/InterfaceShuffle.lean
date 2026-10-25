import Hypernets.Graph.Tensor

/-! The middle-block permutation (A,B,C,D) ↦ (A,C,B,D), preserving wire labels. -/
namespace Hypernets.Graph
namespace InterfaceShuffle
variable {L : Type}

/-- Sum-indexed ports of an ordered concatenation. -/
def ports (I J : List L) : Bijection (Fin I.length ⊕ Fin J.length) (Fin (I ++ J).length) where
  toFun
    | .inl i => Net.Tensor.join I J ⟨false,i⟩
    | .inr j => Net.Tensor.join I J ⟨true,j⟩
  invFun n := match Net.Tensor.split I J n with
    | ⟨false,i⟩ => .inl i
    | ⟨true,j⟩ => .inr j
  left_inv p := by
    cases p <;> simp only [Net.Tensor.split_join]
  right_inv n := by
    have h := Net.Tensor.join_split I J n
    cases split : Net.Tensor.split I J n with
    | mk b i => cases b <;> simpa only [split] using h

@[simp] theorem left_label (I J : List L) (i : Fin I.length) :
    (I ++ J)[(ports I J).toFun (.inl i)] = I[i] :=
  Net.Tensor.join_label I J false i

@[simp] theorem right_label (I J : List L) (i : Fin J.length) :
    (I ++ J)[(ports I J).toFun (.inr i)] = J[i] :=
  Net.Tensor.join_label I J true i

/-- Exchange the middle two summands without changing any local index. -/
def interchange (A B C D : Type) : Bijection ((A ⊕ B) ⊕ (C ⊕ D)) ((A ⊕ C) ⊕ (B ⊕ D)) where
  toFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr b) => .inr (.inl b)
    | .inr (.inl c) => .inl (.inr c)
    | .inr (.inr d) => .inr (.inr d)
  invFun
    | .inl (.inl a) => .inl (.inl a)
    | .inl (.inr c) => .inr (.inl c)
    | .inr (.inl b) => .inl (.inr b)
    | .inr (.inr d) => .inr (.inr d)
  left_inv p := by cases p with | inl p => cases p <;> rfl | inr p => cases p <;> rfl
  right_inv p := by cases p with | inl p => cases p <;> rfl | inr p => cases p <;> rfl

/-- Ordered ports before the exchange. -/
def original (A B C D : List L) :=
  ((ports A B).sum (ports C D)).trans (ports (A ++ B) (C ++ D))

/-- Ordered ports after the exchange, from the same four-component index set. -/
def shuffled (A B C D : List L) :=
  (interchange (Fin A.length) (Fin B.length) (Fin C.length) (Fin D.length)).trans
    (((ports A C).sum (ports B D)).trans (ports (A ++ C) (B ++ D)))

/-- The actual interface permutation, including zero-sized blocks. -/
def bijection (A B C D : List L) :
    Bijection (Fin ((A ++ B) ++ (C ++ D)).length) (Fin ((A ++ C) ++ (B ++ D)).length) :=
  (original A B C D).symm.trans (shuffled A B C D)

theorem component_label (A B C D : List L) (p : (Fin A.length ⊕ Fin B.length) ⊕ (Fin C.length ⊕ Fin D.length)) :
    ((A ++ C) ++ (B ++ D))[(shuffled A B C D).toFun p] =
    ((A ++ B) ++ (C ++ D))[(original A B C D).toFun p] := by
  cases p with
  | inl p => cases p <;> simp only [original, shuffled, interchange, Bijection.trans, Bijection.sum, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, left_label, right_label]
  | inr p => cases p <;> simp only [original, shuffled, interchange, Bijection.trans, Bijection.sum, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, left_label, right_label]

/-- The permutation preserves the wire at every interface position. -/
theorem label (A B C D : List L) (i : Fin ((A ++ B) ++ (C ++ D)).length) :
    ((A ++ C) ++ (B ++ D))[(bijection A B C D).toFun i] = ((A ++ B) ++ (C ++ D))[i] := by
  have h := component_label A B C D ((original A B C D).invFun i)
  simpa only [bijection, Bijection.trans, Bijection.symm, (original A B C D).right_inv] using h

end InterfaceShuffle
end Hypernets.Graph

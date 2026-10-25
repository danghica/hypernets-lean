import Hypernets.Graph.Parallel

/-! Ordered binary parallel composition, with concatenated interfaces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.Tensor
universe u
variable {L : Type}

def interfaces (I J : List L) : Bool → List L
  | false => I
  | true => J

def join (I J : List L) : (Σ b, Fin (interfaces I J b).length) → Fin (I ++ J).length
  | ⟨false,i⟩ => ⟨i.val,by have := i.isLt; change i.val < I.length at this; simp; omega⟩
  | ⟨true,j⟩ => ⟨I.length+j.val,by simp; have := j.isLt; change j.val < J.length at this; omega⟩

def split (I J : List L) (n : Fin (I ++ J).length) : Σ b, Fin (interfaces I J b).length :=
  if h : n.val < I.length then ⟨false,⟨n.val,h⟩⟩
  else ⟨true,⟨n.val-I.length,by have := n.isLt; simp at this; change n.val-I.length < J.length; omega⟩⟩

theorem split_join (I J : List L) (p : Σ b, Fin (interfaces I J b).length) :
    split I J (join I J p) = p := by
  obtain ⟨b,i⟩ := p
  cases b with
  | false => simp [join, split, show i.val < I.length from i.isLt]
  | true => simp [join, split]

theorem join_split (I J : List L) (n : Fin (I ++ J).length) : join I J (split I J n) = n := by
  unfold split
  split <;> apply Fin.ext <;> simp [join] <;> omega

def ports (I J : List L) : Bijection (Σ b, Fin (interfaces I J b).length) (Fin (I ++ J).length) :=
  ⟨join I J,split I J,split_join I J,join_split I J⟩

theorem join_label (I J : List L) (b : Bool) (i : Fin (interfaces I J b).length) :
    (I ++ J)[(join I J ⟨b,i⟩).val] = (interfaces I J b)[i] := by
  cases b with
  | false => simp [join, interfaces]; rfl
  | true => simp [join, interfaces]; rfl

variable {Op : Type u} {σ : Signature L Op} {I O J K : List L}

def family (G : Net σ I O) (H : Net σ J K) : (b : Bool) → Net σ (interfaces I J b) (interfaces O K b)
  | false => G
  | true => H

def boundary (I O J K : List L) : Parallel.Boundary (interfaces I J) (interfaces O K) (I ++ J) (O ++ K) where
  inputs := ports I J
  outputs := ports O K
  input_label := join_label I J
  output_label := join_label O K

/-- Disjoint union with the left graph's ports before the right graph's ports. -/
@[reducible] def net (G : Net σ I O) (H : Net σ J K) : Net σ (I ++ J) (O ++ K) :=
  Parallel.net (family G H) (boundary I O J K) ⟨[false,true],by intro b; cases b <;> simp⟩

/-- Any edge-label property holds exactly when it holds on both factors. -/
theorem labels_iff (G : Net σ I O) (H : Net σ J K) (P : Op → Prop) :
    (∀ e, P ((net G H).edgeLabel e)) ↔ (∀ e, P (G.edgeLabel e)) ∧ ∀ e, P (H.edgeLabel e) := by
  constructor
  · intro h; exact ⟨fun e => h ⟨false,e⟩,fun e => h ⟨true,e⟩⟩
  · rintro ⟨g,h⟩ ⟨b,e⟩; cases b
    · exact g e
    · exact h e

end Hypernets.Graph.Net.Tensor

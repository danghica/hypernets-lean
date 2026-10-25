import Hypernets.Copying.UnaryFragmentRenaming

/-! Coordinates of the original Figure 16 middle-block exchange. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.PairBoundary
open Graph EnvironmentPermutation

def use : Bool → Nat | false => 0 | true => 1

def component {k h} (b : Bool) (j : Fin (environmentInterface k h).length) :
    Σ b, Fin (Net.Tensor.interfaces (environmentInterface k h) (environmentInterface k h) b).length :=
  match b with | false => ⟨false,j⟩ | true => ⟨true,j⟩

/-- Original pair boundary, with only the existing length equality exposed. -/
def index {k h} (b : Bool) (j : Fin (environmentInterface k h).length) :
    Fin (environmentInterface (k*2) (h*2)).length :=
  Fin.cast (congrArg List.length (by simp [environmentInterface,Nat.mul_two]))
    ((Translation.pairBoundary k h).outputs.toFun (component b j))

/-- Every grouped resource position has a component and an original position. -/
theorem index_surjective {k h} (j : Fin (environmentInterface (k*2) (h*2)).length) :
    ∃ b i, index b i = j := by
  let eq : ((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
      (List.replicate h Wire.atom ++ List.replicate h Wire.atom)) = environmentInterface (k*2) (h*2) := by simp [environmentInterface,Nat.mul_two]
  let n := Fin.cast (congrArg List.length eq.symm) j
  have hn := (Translation.pairBoundary k h).outputs.right_inv n
  generalize hp : (Translation.pairBoundary k h).outputs.invFun n = p at hn
  obtain ⟨b,i⟩ := p
  cases b with
  | false => refine ⟨false,i,?_⟩; unfold index component; rw [hn]; rfl
  | true => refine ⟨true,i,?_⟩; unfold index component; rw [hn]; rfl

theorem shuffle_component (A B C D : List Wire)
    (p : (Fin A.length ⊕ Fin B.length) ⊕ (Fin C.length ⊕ Fin D.length)) :
    (InterfaceShuffle.bijection A B C D).toFun ((InterfaceShuffle.original A B C D).toFun p) =
      (InterfaceShuffle.shuffled A B C D).toFun p := by
  change (InterfaceShuffle.shuffled A B C D).toFun
    ((InterfaceShuffle.original A B C D).invFun ((InterfaceShuffle.original A B C D).toFun p)) = _
  rw [Bijection.left_inv]

/-- Term resources retain their use-major position i + k * use. -/
theorem term_index {k h} (b : Bool) (i : Fin k) :
    index (h := h) b (termIndex i) =
      termIndex ⟨i.val+k*use b,by cases b <;> simp [use] <;> omega⟩ := by
  cases b with
  | false =>
      unfold index Translation.pairBoundary
      change Fin.cast _ ((InterfaceShuffle.bijection _ _ _ _).toFun
        ((InterfaceShuffle.original (List.replicate k Wire.term) (List.replicate h Wire.atom)
          (List.replicate k Wire.term) (List.replicate h Wire.atom)).toFun (.inl (.inl ⟨i.val,by simpa using i.isLt⟩)))) = _
      rw [shuffle_component]
      apply Fin.ext
      simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
        Bijection.trans,Bijection.sum,Net.Tensor.join,termIndex,atomIndex,use]
      try omega
  | true =>
      unfold index Translation.pairBoundary
      change Fin.cast _ ((InterfaceShuffle.bijection _ _ _ _).toFun
        ((InterfaceShuffle.original (List.replicate k Wire.term) (List.replicate h Wire.atom)
          (List.replicate k Wire.term) (List.replicate h Wire.atom)).toFun (.inr (.inl ⟨i.val,by simpa using i.isLt⟩)))) = _
      rw [shuffle_component]
      apply Fin.ext
      simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
        Bijection.trans,Bijection.sum,Net.Tensor.join,termIndex,atomIndex,use]
      try omega

theorem atom_join {k h} (a : Fin h) : atomIndex (k := k) a =
    Net.Tensor.join (List.replicate k Wire.term) (List.replicate h Wire.atom) ⟨true,⟨a.val,by simpa [Net.Tensor.interfaces] using a.isLt⟩⟩ := by
  apply Fin.ext
  simp [atomIndex,Net.Tensor.join]

/-- Atom resources remain after both term blocks, with use-major atom order. -/
theorem atom_index {k h} (b : Bool) (a : Fin h) :
    index (k := k) b (atomIndex a) =
      atomIndex ⟨a.val+h*use b,by cases b <;> simp [use] <;> omega⟩ := by
  conv => lhs; rw [atom_join]
  cases b with
  | false =>
      unfold index Translation.pairBoundary
      change Fin.cast _ ((InterfaceShuffle.bijection _ _ _ _).toFun
        ((InterfaceShuffle.original (List.replicate k Wire.term) (List.replicate h Wire.atom)
          (List.replicate k Wire.term) (List.replicate h Wire.atom)).toFun (.inl (.inr ⟨a.val,by simpa using a.isLt⟩)))) = _
      rw [shuffle_component]
      apply Fin.ext
      simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
        Bijection.trans,Bijection.sum,Net.Tensor.join,termIndex,atomIndex,use]
      try omega
  | true =>
      unfold index Translation.pairBoundary
      change Fin.cast _ ((InterfaceShuffle.bijection _ _ _ _).toFun
        ((InterfaceShuffle.original (List.replicate k Wire.term) (List.replicate h Wire.atom)
          (List.replicate k Wire.term) (List.replicate h Wire.atom)).toFun (.inr (.inr ⟨a.val,by simpa using a.isLt⟩)))) = _
      rw [shuffle_component]
      apply Fin.ext
      simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
        Bijection.trans,Bijection.sum,Net.Tensor.join,termIndex,atomIndex,use]
      try omega
end Hypernets.Copying.PairBoundary

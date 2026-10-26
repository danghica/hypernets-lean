import Hypernets.Copying.BinaryRenamingRegression

/-! Typed box-interface permutations, with bound outputs fixed pointwise.
The interface operation is distinct from ordered graph isomorphism. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph EnvironmentPermutation

structure TypedPermutation (O : List Wire) where
  bijection : Bijection (Fin O.length) (Fin O.length)
  typed : ∀ i, O[bijection.toFun i] = O[i]

namespace TypedPermutation
variable {O : List Wire}
def refl (O : List Wire) : TypedPermutation O := ⟨Bijection.refl _, fun _ => rfl⟩
def symm (p : TypedPermutation O) : TypedPermutation O where
  bijection := p.bijection.symm
  typed i := by simpa [Bijection.symm,p.bijection.right_inv] using (p.typed (p.bijection.invFun i)).symm

def trans (p q : TypedPermutation O) : TypedPermutation O where
  bijection := p.bijection.trans q.bijection
  typed i := (q.typed _).trans (p.typed i)

/-- Add a fixed prefix to a permutation of the suffix, including empty blocks. -/
def prefixMap (n : Nat) (f : Fin O.length → Fin O.length) (i : Fin (List.replicate n Wire.term ++ O).length) :
    Fin (List.replicate n Wire.term ++ O).length :=
  if h : i.val < n then ⟨i.val, i.isLt⟩ else
    ⟨n + (f ⟨i.val-n,by have := i.isLt; simp at this; omega⟩).val, by simp⟩

theorem prefixMap_bound (n : Nat) (f : Fin O.length → Fin O.length) (i : Fin n) :
    prefixMap n f ⟨i.val,by simp; omega⟩ = ⟨i.val,by simp; omega⟩ := by
  simp [prefixMap,i.isLt]

theorem prefixMap_free (n : Nat) (f : Fin O.length → Fin O.length) (i : Fin O.length) :
    prefixMap n f ⟨n+i.val,by simp⟩ = ⟨n+(f i).val,by simp⟩ := by
  simp [prefixMap,show ¬ n+i.val < n by omega]

/-- Prefix extension is a typed bijection, not merely an injective renaming. -/
def extend (n : Nat) (p : TypedPermutation O) : TypedPermutation (List.replicate n .term ++ O) where
  bijection := {
    toFun := prefixMap n p.bijection.toFun
    invFun := prefixMap n p.bijection.invFun
    left_inv i := by
      by_cases hi : i.val < n
      · simp [prefixMap,hi]
      · let j : Fin O.length := ⟨i.val-n,by have := i.isLt; simp at this; omega⟩
        have eq : i = ⟨n+j.val,by simp⟩ := Fin.ext (by dsimp [j]; omega)
        rw [eq,prefixMap_free,prefixMap_free,p.bijection.left_inv]
    right_inv i := by
      by_cases hi : i.val < n
      · simp [prefixMap,hi]
      · let j : Fin O.length := ⟨i.val-n,by have := i.isLt; simp at this; omega⟩
        have eq : i = ⟨n+j.val,by simp⟩ := Fin.ext (by dsimp [j]; omega)
        rw [eq,prefixMap_free,prefixMap_free,p.bijection.right_inv] }
  typed i := by
    by_cases hi : i.val < n
    · simp [prefixMap,hi]
    · let j : Fin O.length := ⟨i.val-n,by have := i.isLt; simp at this; omega⟩
      have eq : i = ⟨n+j.val,by simp⟩ := Fin.ext (by dsimp [j]; omega)
      rw [eq]
      change (List.replicate n Wire.term ++ O)[(prefixMap n p.bijection.toFun _).val] = _
      simpa [prefixMap_free,List.getElem_append,show ¬ n+(p.bijection.toFun j).val < n by omega,show ¬ n+j.val < n by omega] using p.typed j

/-- Equality transport of an interface changes no numerical position. -/
def cast {O K : List Wire} (eq : O = K) (p : TypedPermutation O) : TypedPermutation K := eq ▸ p

/-- The two free resource sorts induce their exact combined boundary action. -/
def environment {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    TypedPermutation (environmentInterface k h) :=
  ⟨(MultiUseBoundary.iso 0 1 ρ α).outputs, (MultiUseBoundary.iso 0 1 ρ α).output_label⟩

theorem environment_term {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (i : Fin k) :
    (environment ρ α).bijection.toFun (termIndex i) = termIndex (ρ.toFun i) := by
  have q := MultiUseBoundary.output_term 0 1 ρ α i
  rw [BoundaryIso.map_output] at q
  exact Port.output.inj q

theorem environment_atom {k h} (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    (environment ρ α).bijection.toFun (atomIndex a) = atomIndex (α.toFun a) := by
  have q := MultiUseBoundary.output_atom 0 1 ρ α a
  rw [BoundaryIso.map_output] at q
  exact Port.output.inj q
theorem cast_val {O K : List Wire} (eq : O = K) (p : TypedPermutation O) (i : Fin K.length) :
    ((cast eq p).bijection.toFun i).val =
      (p.bijection.toFun (Fin.cast (congrArg List.length eq.symm) i)).val := by cases eq; rfl
end TypedPermutation

namespace BoxPermutation
/-- Body boundary equals a bound prefix followed by the entire free interface. -/
theorem interface_split (n k h : Nat) :
    environmentInterface (n+k) h = List.replicate n .term ++ environmentInterface k h := by
  simp only [environmentInterface,← List.replicate_append_replicate,List.append_assoc]

/-- The uniquely determined inner permutation extends the free permutation by identity. -/
def inner {k h} (n : Nat) (p : TypedPermutation (environmentInterface k h)) :
    TypedPermutation (environmentInterface (n+k) h) :=
  TypedPermutation.cast (interface_split n k h).symm (p.extend n)

def boundIndex {n k h} (i : Fin n) : Fin (environmentInterface (n+k) h).length :=
  ⟨i.val,by simp [environmentInterface]; omega⟩
def freeIndex {n k h} (i : Fin (environmentInterface k h).length) : Fin (environmentInterface (n+k) h).length :=
  ⟨n+i.val,by have := i.isLt; simp_all [environmentInterface]; omega⟩

/-- A pair records both interfaces and their exact numerical correspondence. -/
structure Pair (n k h : Nat) where
  outer : TypedPermutation (environmentInterface k h)
  body : TypedPermutation (environmentInterface (n+k) h)
  bound : ∀ i, body.bijection.toFun (boundIndex i) = boundIndex i
  free : ∀ i, body.bijection.toFun (freeIndex i) = freeIndex (outer.bijection.toFun i)

theorem inner_bound {n k h} (p : TypedPermutation (environmentInterface k h)) (i : Fin n) :
    (inner n p).bijection.toFun (boundIndex i) = boundIndex i := by
  apply Fin.ext
  rw [inner,TypedPermutation.cast_val]
  change (TypedPermutation.prefixMap n p.bijection.toFun _).val = i.val
  simp [TypedPermutation.prefixMap,boundIndex,i.isLt]

theorem inner_free {n k h} (p : TypedPermutation (environmentInterface k h)) (i : Fin (environmentInterface k h).length) :
    (inner n p).bijection.toFun (freeIndex i) = freeIndex (p.bijection.toFun i) := by
  apply Fin.ext
  rw [inner,TypedPermutation.cast_val]
  change (TypedPermutation.prefixMap n p.bijection.toFun _).val = n+(p.bijection.toFun i).val
  simp [TypedPermutation.prefixMap,freeIndex,show ¬ n+i.val < n by omega]

def pair {k h} (n : Nat) (p : TypedPermutation (environmentInterface k h)) : Pair n k h :=
  ⟨p,inner n p,inner_bound p,inner_free p⟩

/-- The conditions determine the body action at every position. -/
theorem Pair.unique {n k h} (p : Pair n k h) (j : Fin (environmentInterface (n+k) h).length) :
    p.body.bijection.toFun j = (inner n p.outer).bijection.toFun j := by
  by_cases hj : j.val < n
  · let i : Fin n := ⟨j.val,hj⟩
    have eq : j = boundIndex (k := k) (h := h) i := rfl
    rw [eq,p.bound,inner_bound]
  · let i : Fin (environmentInterface k h).length := ⟨j.val-n,by have := j.isLt; simp_all [environmentInterface]; omega⟩
    have eq : j = freeIndex (n := n) i := Fin.ext (by dsimp [i,freeIndex]; omega)
    rw [eq,p.free,inner_free]

def Pair.symm {n k h} (p : Pair n k h) : Pair n k h where
  outer := p.outer.symm
  body := p.body.symm
  bound i := by
    change p.body.bijection.invFun (boundIndex i) = boundIndex i
    have eq := congrArg p.body.bijection.invFun (p.bound i)
    simpa [p.body.bijection.left_inv] using eq.symm
  free i := by
    have eq := congrArg p.body.bijection.invFun (p.free (p.outer.bijection.invFun i))
    simpa [p.body.bijection.left_inv,p.outer.bijection.right_inv,TypedPermutation.symm,Bijection.symm] using eq.symm

def Pair.trans {n k h} (p q : Pair n k h) : Pair n k h where
  outer := p.outer.trans q.outer
  body := p.body.trans q.body
  bound i := by change q.body.bijection.toFun (p.body.bijection.toFun _) = _; rw [p.bound,q.bound]
  free i := by change q.body.bijection.toFun (p.body.bijection.toFun _) = _; rw [p.free,q.free]; rfl
end BoxPermutation
end Hypernets.Copying

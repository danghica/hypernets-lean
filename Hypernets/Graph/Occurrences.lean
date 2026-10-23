import Hypernets.Graph.DeepPlugging

/-! Incidence-independent occurrence fibres, and exact hole-preserving provenance. -/

namespace Hypernets.Linear

open Graph

variable {Op : Type} {ops : Operations Op}

/-- Child occurrences depend only on an edge's label, not its surrounding graph. -/
def Children (ops : Operations Op) : (d : Nat) → (alphabet ops d).Symbol → Type
  | 0 => fun _ => Empty
  | d + 1 => fun label => match label with
    | .inl _ => Empty
    | .inr b => AllEdge ops d b.body

/-- The shallow occurrence of an edge and every occurrence inside its label. -/
abbrev Fiber (ops : Operations Op) (d : Nat) (label : (alphabet ops d).Symbol) :=
  Unit ⊕ Children ops d label

def shallowHole (ops : Operations Op) : (d : Nat) → (alphabet ops d).Symbol → Option Hole
  | 0, p => primitiveHole p.down
  | _ + 1, .inl p => primitiveHole p
  | _ + 1, .inr _ => none

def childHole (ops : Operations Op) : (d : Nat) → (label : (alphabet ops d).Symbol) →
    Children ops d label → Option Hole
  | 0, _, x => nomatch x
  | _ + 1, .inl _, x => nomatch x
  | d + 1, .inr b, x => holeAt ops d b.body x

def fiberHole (ops : Operations Op) (d : Nat) (label : (alphabet ops d).Symbol) :
    Fiber ops d label → Option Hole
  | .inl _ => shallowHole ops d label
  | .inr x => childHole ops d label x

/-- Every occurrence is equivalently its outer edge and a label-local address. -/
abbrev Occurrences {d I O} (G : Hypernet ops d I O) :=
  Σ e : G.Edge, Fiber ops d (G.edgeLabel e)

def occurrenceBijection (ops : Operations Op) (d : Nat) {I O} (G : Hypernet ops d I O) :
    Bijection (AllEdge ops d G) (Occurrences G) := by
  cases d with
  | zero => exact {
      toFun e := ⟨e, .inl ()⟩
      invFun a := a.1
      left_inv _ := rfl
      right_inv := by rintro ⟨e, x | x⟩; cases x; rfl; exact nomatch x
    }
  | succ d => exact {
      toFun a := match a with
        | .inl e => ⟨e, .inl ()⟩
        | .inr ⟨e, x⟩ => ⟨e, .inr x⟩
      invFun a := match a with
        | ⟨e, .inl _⟩ => .inl e
        | ⟨e, .inr x⟩ => .inr ⟨e, x⟩
      left_inv := by rintro (e | ⟨e, x⟩) <;> rfl
      right_inv := by rintro ⟨e, x | x⟩; cases x; rfl; rfl
    }

def occurrenceHole {d I O} (G : Hypernet ops d I O) (a : Occurrences G) : Option Hole :=
  fiberHole ops d (G.edgeLabel a.1) a.2

theorem occurrenceBijection_hole (d : Nat) {I O} (G : Hypernet ops d I O)
    (a : AllEdge ops d G) :
    occurrenceHole G ((occurrenceBijection ops d G).toFun a) = holeAt ops d G a := by
  cases d with
  | zero => rfl
  | succ d =>
      cases a with
      | inl e => cases h : G.edgeLabel e <;> simp [occurrenceHole, occurrenceBijection, fiberHole, shallowHole, holeAt, h]
      | inr a =>
          obtain ⟨e, x⟩ := a
          simp only [occurrenceHole, occurrenceBijection, fiberHole, childHole, holeAt]
          generalize G.edgeLabel e = label at x ⊢
          cases label <;> rfl

/-- The existing context condition, expressed in label-local coordinates. -/
theorem uniqueHoles_iff_occurrences {d I O} (G : Hypernet ops d I O) :
    UniqueHoles ops d G ↔
      ∀ h (a b : Occurrences G), occurrenceHole G a = some h →
        occurrenceHole G b = some h → a = b := by
  let f := occurrenceBijection ops d G
  have preserves := occurrenceBijection_hole (ops := ops) d G
  constructor
  · intro unique h a b ha hb
    have a' := preserves (f.invFun a)
    have b' := preserves (f.invFun b)
    rw [f.right_inv] at a' b'
    have eq := unique h (f.invFun a) (f.invFun b) (a'.symm.trans ha) (b'.symm.trans hb)
    have := congrArg f.toFun eq
    simpa [f.right_inv] using this
  · intro unique h a b ha hb
    exact f.injective (unique h (f.toFun a) (f.toFun b)
      ((preserves a).trans ha) ((preserves b).trans hb))

theorem fiberHole_transport {d} {a b : (alphabet ops d).Symbol} (h : a = b)
    (x : Fiber ops d a) : fiberHole ops d b (h ▸ x) = fiberHole ops d a x := by
  cases h
  rfl

theorem fiber_transport_injective {d} {a b : (alphabet ops d).Symbol} (h : a = b)
    {x y : Fiber ops d a} (eq : h ▸ x = h ▸ y) : x = y := by
  cases h
  exact eq

/-- An injective label-preserving map of shallow edges transports all occurrences. -/
def mapOccurrences {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : G.Edge → H.Edge) (labels : ∀ e, G.edgeLabel e = H.edgeLabel (f e)) :
    Occurrences G → Occurrences H
  | ⟨e, x⟩ => ⟨f e, labels e ▸ x⟩

theorem mapOccurrences_hole {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : G.Edge → H.Edge) (labels : ∀ e, G.edgeLabel e = H.edgeLabel (f e))
    (a : Occurrences G) :
    occurrenceHole H (mapOccurrences f labels a) = occurrenceHole G a := by
  obtain ⟨e, x⟩ := a
  exact fiberHole_transport (labels e) x

theorem mapOccurrences_injective {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : G.Edge → H.Edge) (labels : ∀ e, G.edgeLabel e = H.edgeLabel (f e))
    (inj : ∀ a b, f a = f b → a = b)
    {a b : Occurrences G} (eq : mapOccurrences f labels a = mapOccurrences f labels b) : a = b := by
  obtain ⟨e, x⟩ := a
  obtain ⟨f', y⟩ := b
  have ef := inj e f' (congrArg Sigma.fst eq)
  subst f'
  have h := (Sigma.mk.inj eq).2
  have : x = y := fiber_transport_injective (labels e) (eq_of_heq h)
  subst y
  rfl

end Hypernets.Linear

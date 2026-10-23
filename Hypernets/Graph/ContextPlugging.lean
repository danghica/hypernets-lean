import Hypernets.Graph.Occurrences

/-! Hole inventories and freshness-preserving context composition. -/

namespace Hypernets.Linear

open Graph

variable {Op : Type} {ops : Operations Op}

def HasHole {d I O} (G : Hypernet ops d I O) (h : Hole) : Prop :=
  ∃ a, holeAt ops d G a = some h

def HoleFree {d I O} (G : Hypernet ops d I O) : Prop :=
  ∀ h, ¬ HasHole G h

/-- Full-label disjointness, including occurrences at every nesting depth. -/
def HolesDisjoint {d d' I O J K} (G : Hypernet ops d I O) (H : Hypernet ops d' J K) : Prop :=
  ∀ h, HasHole G h → HasHole H h → False

theorem hasHole_iff_occurrences {d I O} (G : Hypernet ops d I O) (h : Hole) :
    HasHole G h ↔ ∃ a : Occurrences G, occurrenceHole G a = some h := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(occurrenceBijection ops d G).toFun a,
      (occurrenceBijection_hole d G a).trans ha⟩
  · rintro ⟨a, ha⟩
    refine ⟨(occurrenceBijection ops d G).invFun a, ?_⟩
    have eq := occurrenceBijection_hole d G ((occurrenceBijection ops d G).invFun a)
    rw [(occurrenceBijection ops d G).right_inv] at eq
    exact eq.symm.trans ha

theorem holeFree_unique {d I O} {G : Hypernet ops d I O} (free : HoleFree G) :
    UniqueHoles ops d G := by
  intro h a _ ha _
  exact False.elim (free h ⟨a, ha⟩)

theorem HolesDisjoint.symm {d d' I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d' J K}
    (disjoint : HolesDisjoint G H) : HolesDisjoint H G :=
  fun h hh hg => disjoint h hg hh

theorem holeFree_disjoint {d d' I O J K} (G : Hypernet ops d I O)
    {H : Hypernet ops d' J K} (free : HoleFree H) : HolesDisjoint G H :=
  fun h _ hh => free h hh

/-- Boxing neither creates nor removes hole labels in its body. -/
theorem box_hasHole_iff {d bound free}
    (body : Hypernet ops d [.term] (List.replicate (bound + free) .term)) (h : Hole) :
    HasHole (box (bound := bound) (free := free) body) h ↔ HasHole body h := by
  constructor
  · rintro ⟨a, ha⟩
    cases a with
    | inl e => cases ha
    | inr a =>
        obtain ⟨e, x⟩ := a
        exact ⟨x, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨.inr ⟨0, a⟩, ha⟩

theorem box_holeFree {d bound free}
    (body : Hypernet ops d [.term] (List.replicate (bound + free) .term))
    (hf : HoleFree body) : HoleFree (box (bound := bound) (free := free) body) :=
  fun h hh => hf h ((box_hasHole_iff body h).mp hh)

/-- Hole inventories are preserved by label-preserving edge maps. -/
theorem hasHole_map {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : G.Edge → H.Edge) (labels : ∀ e, G.edgeLabel e = H.edgeLabel (f e)) {h}
    (present : HasHole G h) : HasHole H h := by
  obtain ⟨a, ha⟩ := (hasHole_iff_occurrences G h).mp present
  exact (hasHole_iff_occurrences H h).mpr
    ⟨mapOccurrences f labels a, (mapOccurrences_hole f labels a).trans ha⟩

/-- Unique holes reflect along injective label-preserving edge maps. -/
theorem uniqueHoles_of_embedding {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : G.Edge → H.Edge) (labels : ∀ e, G.edgeLabel e = H.edgeLabel (f e))
    (inj : ∀ a b, f a = f b → a = b) (unique : UniqueHoles ops d H) :
    UniqueHoles ops d G := by
  apply (uniqueHoles_iff_occurrences G).mpr
  intro h a b ha hb
  apply mapOccurrences_injective f labels inj
  exact (uniqueHoles_iff_occurrences H).mp unique h _ _
    ((mapOccurrences_hole f labels a).trans ha) ((mapOccurrences_hole f labels b).trans hb)

theorem iso_hasHole_iff {d I O} {G H : Hypernet ops d I O} (f : Net.Iso G H) (h : Hole) :
    HasHole G h ↔ HasHole H h :=
  ⟨hasHole_map f.edges.toFun (fun e => (f.edge_label e).symm),
    hasHole_map f.symm.edges.toFun (fun e => (f.symm.edge_label e).symm)⟩

theorem iso_uniqueHoles_iff {d I O} {G H : Hypernet ops d I O} (f : Net.Iso G H) :
    UniqueHoles ops d G ↔ UniqueHoles ops d H :=
  ⟨uniqueHoles_of_embedding f.symm.edges.toFun (fun e => (f.symm.edge_label e).symm)
      (fun _ _ h => f.symm.edges.injective h),
    uniqueHoles_of_embedding f.edges.toFun (fun e => (f.edge_label e).symm)
      (fun _ _ h => f.edges.injective h)⟩

/-- Every new occurrence has a distinct old or inserted origin, with the same
hole lookup. This records provenance, rather than presupposing context closure. -/
structure Provenance {d d' d'' I O J K P Q}
    (result : Hypernet ops d I O) (host : Hypernet ops d' J K)
    (replacement : Hypernet ops d'' P Q) where
  origin : Occurrences result → Occurrences host ⊕ Occurrences replacement
  injective : ∀ {a b}, origin a = origin b → a = b
  hole : ∀ a, occurrenceHole result a =
    match origin a with
    | .inl old => occurrenceHole host old
    | .inr new => occurrenceHole replacement new

namespace Provenance

variable {d d' d'' I O J K P Q} {R : Hypernet ops d I O}
    {C : Hypernet ops d' J K} {H : Hypernet ops d'' P Q}

theorem holes_subset (p : Provenance R C H) {h} (hh : HasHole R h) :
    HasHole C h ∨ HasHole H h := by
  obtain ⟨a, ha⟩ := (hasHole_iff_occurrences R h).mp hh
  rw [p.hole a] at ha
  cases eq : p.origin a with
  | inl old => exact .inl ((hasHole_iff_occurrences C h).mpr ⟨old, by simpa [eq] using ha⟩)
  | inr new => exact .inr ((hasHole_iff_occurrences H h).mpr ⟨new, by simpa [eq] using ha⟩)

/-- Freshness needs to inspect only host occurrences actually retained. -/
def Compatible (p : Provenance R C H) : Prop :=
  ∀ h (a : Occurrences R) (old : Occurrences C), p.origin a = .inl old →
    occurrenceHole C old = some h → HasHole H h → False

theorem unique_of_compatible (p : Provenance R C H) (uc : UniqueHoles ops d' C)
    (uh : UniqueHoles ops d'' H) (fresh : p.Compatible) : UniqueHoles ops d R := by
  apply (uniqueHoles_iff_occurrences R).mpr
  intro h a b ha hb
  rw [p.hole a] at ha
  rw [p.hole b] at hb
  apply p.injective
  cases ea : p.origin a with
  | inl old =>
      cases eb : p.origin b with
      | inl old' =>
          have eq := (uniqueHoles_iff_occurrences C).mp uc h old old'
            (by simpa [ea] using ha) (by simpa [eb] using hb)
          exact congrArg Sum.inl eq
      | inr new =>
          exact False.elim (fresh h a old ea (by simpa [ea] using ha)
            ((hasHole_iff_occurrences H h).mpr ⟨new, by simpa [eb] using hb⟩))
  | inr new =>
      cases eb : p.origin b with
      | inl old =>
          exact False.elim (fresh h b old eb (by simpa [eb] using hb)
            ((hasHole_iff_occurrences H h).mpr ⟨new, by simpa [ea] using ha⟩))
      | inr new' =>
          have eq := (uniqueHoles_iff_occurrences H).mp uh h new new'
            (by simpa [ea] using ha) (by simpa [eb] using hb)
          exact congrArg Sum.inr eq


theorem unique (p : Provenance R C H) (uc : UniqueHoles ops d' C)
    (uh : UniqueHoles ops d'' H) (fresh : HolesDisjoint C H) : UniqueHoles ops d R :=
  p.unique_of_compatible uc uh (fun h _ old _ present hh =>
    fresh h ((hasHole_iff_occurrences C h).mpr ⟨old, present⟩) hh)

end Provenance

/-- Shallow plugging retains every occurrence under a surviving host edge and
inserts every replacement occurrence, including all descendants of box labels. -/
def shallowProvenance {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) :
    Provenance (C.plug hole H) C H where
  origin a := match a with
    | ⟨.inl e, x⟩ => .inl ⟨e.val, x⟩
    | ⟨.inr e, x⟩ => .inr ⟨e, x⟩
  injective := by
    rintro ⟨e, x⟩ ⟨f, y⟩ eq
    cases e with
    | inl e =>
        cases f with
        | inl f =>
            have pair := Sum.inl.inj eq
            have ef : e = f := Subtype.ext (congrArg Sigma.fst pair)
            subst f
            have xy : x = y := eq_of_heq (Sigma.mk.inj pair).2
            subst y
            rfl
        | inr f => cases eq
    | inr e =>
        cases f with
        | inl f => cases eq
        | inr f =>
            have pair := Sum.inr.inj eq
            cases pair
            rfl
  hole := by rintro ⟨e | e, x⟩ <;> rfl

/-- Context closure for arbitrary shallow edges, under full-label freshness. -/
theorem plug_uniqueHoles {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (uc : UniqueHoles ops d C) (uh : UniqueHoles ops d H) (fresh : HolesDisjoint C H) :
    UniqueHoles ops d (C.plug hole H) :=
  (shallowProvenance C hole H).unique uc uh fresh

noncomputable def Context.plug {d I O} (C : Context ops d I O) (hole : C.val.Edge)
    (H : Context ops d ((alphabet ops d).signature.input (C.val.edgeLabel hole))
      ((alphabet ops d).signature.output (C.val.edgeLabel hole)))
    (fresh : HolesDisjoint C.val H.val) : Context ops d I O :=
  ⟨C.val.plug hole H.val, plug_uniqueHoles C.val hole H.val C.property H.property fresh⟩

/-- A hole occurrence under an outer edge that survives the selected replacement. -/
def RetainedHole {d I O} (C : Hypernet ops d I O) (removed : C.Edge) (h : Hole) : Prop :=
  ∃ e : C.Edge, e ≠ removed ∧ ∃ x : Fiber ops d (C.edgeLabel e),
    fiberHole ops d (C.edgeLabel e) x = some h

/-- Exact hole-label inventory after shallow plugging, including deep holes. -/
theorem plug_hasHole_iff {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) (h : Hole) :
    HasHole (C.plug hole H) h ↔ RetainedHole C hole h ∨ HasHole H h := by
  rw [hasHole_iff_occurrences]
  constructor
  · rintro ⟨⟨e, x⟩, ha⟩
    cases e with
    | inl e => exact .inl ⟨e.val, e.property, x, ha⟩
    | inr e => exact .inr ((hasHole_iff_occurrences H h).mpr ⟨⟨e, x⟩, ha⟩)
  · intro present
    cases present with
    | inl retained =>
        obtain ⟨e, ne, x, hx⟩ := retained
        exact ⟨⟨.inl ⟨e, ne⟩, x⟩, hx⟩
    | inr inserted =>
        obtain ⟨⟨e, x⟩, hx⟩ := (hasHole_iff_occurrences H h).mp inserted
        exact ⟨⟨.inr e, x⟩, hx⟩

/-- Sharp freshness condition: labels below the removed edge are irrelevant. -/
def PlugFresh {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole))) : Prop :=
  ∀ h, RetainedHole C hole h → HasHole H h → False

theorem plug_uniqueHoles_of_fresh {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (uc : UniqueHoles ops d C) (uh : UniqueHoles ops d H) (fresh : PlugFresh C hole H) :
    UniqueHoles ops d (C.plug hole H) := by
  apply (shallowProvenance C hole H).unique_of_compatible uc uh
  rintro h ⟨e, x⟩ old origin present inserted
  cases e with
  | inl e =>
      have pair := Sum.inl.inj origin
      cases pair
      exact fresh h ⟨e.val, e.property, x, present⟩ inserted
  | inr e => cases origin

/-- Any collision between a retained and an inserted hole violates uniqueness. -/
theorem plug_fresh_necessary {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (unique : UniqueHoles ops d (C.plug hole H)) : PlugFresh C hole H := by
  rintro h ⟨e, ne, x, hx⟩ inserted
  obtain ⟨⟨f, y⟩, hy⟩ := (hasHole_iff_occurrences H h).mp inserted
  have eq := (uniqueHoles_iff_occurrences (C.plug hole H)).mp unique h
    ⟨.inl ⟨e, ne⟩, x⟩ ⟨.inr f, y⟩ hx hy
  have bad := congrArg Sigma.fst eq
  cases bad

/-- For two certified input contexts, sharp freshness is necessary and sufficient. -/
theorem plug_uniqueHoles_iff_fresh {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (uc : UniqueHoles ops d C) (uh : UniqueHoles ops d H) :
    UniqueHoles ops d (C.plug hole H) ↔ PlugFresh C hole H :=
  ⟨plug_fresh_necessary C hole H, plug_uniqueHoles_of_fresh C hole H uc uh⟩

/-- In a context, the label of a removed shallow hole cannot survive elsewhere. -/
theorem removed_hole_not_retained {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (unique : UniqueHoles ops d C) (h : Hole)
    (selected : shallowHole ops d (C.edgeLabel hole) = some h) : ¬ RetainedHole C hole h := by
  rintro ⟨e, ne, x, hx⟩
  have eq := (uniqueHoles_iff_occurrences C).mp unique h ⟨e, x⟩ ⟨hole, .inl ()⟩ hx selected
  exact ne (congrArg Sigma.fst eq)

/-- A consumed hole label remains exactly when the replacement reintroduces it. -/
theorem plug_consumed_hole_iff {d I O} (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (unique : UniqueHoles ops d C) (h : Hole)
    (selected : shallowHole ops d (C.edgeLabel hole) = some h) :
    HasHole (C.plug hole H) h ↔ HasHole H h := by
  rw [plug_hasHole_iff]
  exact or_iff_right (removed_hole_not_retained C hole unique h selected)

noncomputable def Context.plugFresh {d I O} (C : Context ops d I O) (hole : C.val.Edge)
    (H : Context ops d ((alphabet ops d).signature.input (C.val.edgeLabel hole))
      ((alphabet ops d).signature.output (C.val.edgeLabel hole)))
    (fresh : PlugFresh C.val hole H.val) : Context ops d I O :=
  ⟨C.val.plug hole H.val, plug_uniqueHoles_of_fresh C.val hole H.val C.property H.property fresh⟩

end Hypernets.Linear

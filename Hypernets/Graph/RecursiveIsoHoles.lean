import Hypernets.Graph.RecursiveIso

/-! Hole observations and context validity are invariant under recursive renaming. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- An injective map of label positions preserving the complete hole observation. -/
structure FiberEmbedding {d} (a b : (alphabet ops d).Symbol) where
  map : Fiber ops d a → Fiber ops d b
  injective : ∀ {x y}, map x = map y → x = y
  hole : ∀ x, fiberHole ops d b (map x) = fiberHole ops d a x

/-- An injective map of graph occurrences preserving hole observations. -/
structure HoleEmbedding {d I O J K} (G : Hypernet ops d I O) (H : Hypernet ops d J K) where
  map : Occurrences G → Occurrences H
  injective : ∀ {x y}, map x = map y → x = y
  hole : ∀ x, occurrenceHole H (map x) = occurrenceHole G x

/-- Assemble injective fibre maps over an injective map of outer edges. -/
def HoleEmbedding.ofFibers {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (edges : G.Edge → H.Edge) (inj : ∀ {e f}, edges e = edges f → e = f)
    (fibres : ∀ e, FiberEmbedding (G.edgeLabel e) (H.edgeLabel (edges e))) : HoleEmbedding G H where
  map a := ⟨edges a.1, (fibres a.1).map a.2⟩
  injective := by
    rintro ⟨e, x⟩ ⟨f, y⟩ eq
    have ef : e = f := inj (congrArg Sigma.fst eq)
    subst f
    have xy : x = y := (fibres e).injective (eq_of_heq (Sigma.mk.inj eq).2)
    subst y
    rfl
  hole a := (fibres a.1).hole a.2

/-- Translate an occurrence embedding back to the original deep-address coordinates. -/
def HoleEmbedding.allEdge {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : HoleEmbedding G H) (a : AllEdge ops d G) : AllEdge ops d H :=
  (occurrenceBijection ops d H).invFun (f.map ((occurrenceBijection ops d G).toFun a))

theorem HoleEmbedding.allEdge_injective {d I O J K} {G : Hypernet ops d I O}
    {H : Hypernet ops d J K} (f : HoleEmbedding G H) {a b : AllEdge ops d G}
    (eq : f.allEdge a = f.allEdge b) : a = b := by
  apply (occurrenceBijection ops d G).injective
  apply f.injective
  have h := congrArg (occurrenceBijection ops d H).toFun eq
  simpa [HoleEmbedding.allEdge, (occurrenceBijection ops d H).right_inv] using h

theorem HoleEmbedding.allEdge_hole {d I O J K} {G : Hypernet ops d I O}
    {H : Hypernet ops d J K} (f : HoleEmbedding G H) (a : AllEdge ops d G) :
    holeAt ops d H (f.allEdge a) = holeAt ops d G a := by
  have h := occurrenceBijection_hole (ops := ops) d H (f.allEdge a)
  rw [HoleEmbedding.allEdge, (occurrenceBijection ops d H).right_inv, f.hole,
    occurrenceBijection_hole] at h
  exact h.symm

/-- Recursively related labels admit concrete injective, observation-preserving
maps of their positions. The body isomorphism is chosen from its existence proof. -/
theorem labelEquiv_hasEmbedding (ops : Operations Op) (d : Nat)
    {a b : (alphabet ops d).Symbol} (related : LabelEquiv ops d a b) : Nonempty (FiberEmbedding a b) := by
  induction d with
  | zero =>
    cases related
    exact ⟨⟨id, fun h => h, fun _ => rfl⟩⟩
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b =>
        cases related
        exact ⟨⟨id, fun h => h, fun _ => rfl⟩⟩
      | inr b => exact False.elim related
    | inr a => cases b with
      | inl b => exact False.elim related
      | inr b =>
        cases related with
        | bodies related =>
          let f := Classical.choice related
          let children := HoleEmbedding.ofFibers f.edges.toFun (fun h => f.edges.injective h)
            (fun e => Classical.choice (ih (f.edge_label e)))
          exact ⟨{
            map := fun x => match x with
              | .inl u => .inl u
              | .inr child => .inr (children.allEdge child)
            injective := by
              intro x y eq
              cases x with
              | inl x => cases y with
                | inl y => exact congrArg Sum.inl (Sum.inl.inj eq)
                | inr y => cases eq
              | inr x => cases y with
                | inl y => cases eq
                | inr y => exact congrArg Sum.inr (children.allEdge_injective (Sum.inr.inj eq))
            hole := by
              intro x
              cases x with
              | inl x => rfl
              | inr x => exact children.allEdge_hole x
          }⟩

/-- Choose an injective, observation-preserving fibre transport. -/
noncomputable def labelEquiv_embedding (ops : Operations Op) (d : Nat)
    {a b : (alphabet ops d).Symbol} (related : LabelEquiv ops d a b) : FiberEmbedding a b :=
  Classical.choice (labelEquiv_hasEmbedding ops d related)

/-- A recursive isomorphism transports all occurrences, not merely outer edges. -/
noncomputable def DeepIso.holeEmbedding {d I O} {G H : Hypernet ops d I O}
    (f : DeepIso G H) : HoleEmbedding G H :=
  HoleEmbedding.ofFibers f.edges.toFun (fun h => f.edges.injective h)
    (fun e => labelEquiv_embedding ops d (f.edge_label e))

/-- Hole presence transports along any observation-preserving occurrence embedding. -/
theorem HoleEmbedding.hasHole {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : HoleEmbedding G H) {h} (present : HasHole G h) : HasHole H h := by
  obtain ⟨a, ha⟩ := (hasHole_iff_occurrences G h).mp present
  exact (hasHole_iff_occurrences H h).mpr ⟨f.map a, (f.hole a).trans ha⟩

/-- Unique hole observations reflect along an injective occurrence map. -/
theorem HoleEmbedding.unique {d I O J K} {G : Hypernet ops d I O} {H : Hypernet ops d J K}
    (f : HoleEmbedding G H) (unique : UniqueHoles ops d H) : UniqueHoles ops d G := by
  apply (uniqueHoles_iff_occurrences G).mpr
  intro h a b ha hb
  apply f.injective
  exact (uniqueHoles_iff_occurrences H).mp unique h (f.map a) (f.map b)
    ((f.hole a).trans ha) ((f.hole b).trans hb)

/-- Independent renaming at every box depth preserves the complete hole inventory. -/
theorem DeepIso.hasHole_iff {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H) (h : Hole) :
    HasHole G h ↔ HasHole H h :=
  ⟨(DeepIso.holeEmbedding f).hasHole, (DeepIso.holeEmbedding (DeepIso.symm f)).hasHole⟩

/-- Recursive isomorphism preserves the context condition at every nesting depth. -/
theorem DeepIso.uniqueHoles_iff {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H) :
    UniqueHoles ops d G ↔ UniqueHoles ops d H :=
  ⟨(DeepIso.holeEmbedding (DeepIso.symm f)).unique, (DeepIso.holeEmbedding f).unique⟩

theorem DeepIso.holeFree_iff {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H) :
    HoleFree G ↔ HoleFree H :=
  ⟨fun free h hh => free h ((DeepIso.hasHole_iff f h).mpr hh),
    fun free h hg => free h ((DeepIso.hasHole_iff f h).mp hg)⟩

end Hypernets.Linear

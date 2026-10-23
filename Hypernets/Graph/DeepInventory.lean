import Hypernets.Graph.DeepContext

/-! Exact inventories and necessary-and-sufficient freshness at arbitrary depth. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- The hole labels carried by one edge, including all its descendants. -/
def EdgeHasHole {d I O} (G : Hypernet ops d I O) (e : G.Edge) (h : Hole) : Prop :=
  ∃ x : Fiber ops d (G.edgeLabel e), fiberHole ops d (G.edgeLabel e) x = some h

/-- Hole uniqueness restricted to occurrences outside one selected edge. -/
def AwayUnique {d I O} (G : Hypernet ops d I O) (e : G.Edge) : Prop :=
  ∀ h (a b : Occurrences G), a.1 ≠ e → b.1 ≠ e →
    occurrenceHole G a = some h → occurrenceHole G b = some h → a = b

/-- Decompose uniqueness into the unaffected edges, the selected fibre, and
absence of collisions between them. -/
theorem uniqueHoles_partition {d I O} (G : Hypernet ops d I O) (e : G.Edge) :
    UniqueHoles ops d G ↔ AwayUnique G e ∧
      (∀ h (x y : Fiber ops d (G.edgeLabel e)),
        fiberHole ops d (G.edgeLabel e) x = some h →
        fiberHole ops d (G.edgeLabel e) y = some h → x = y) ∧
      (∀ h, RetainedHole G e h → EdgeHasHole G e h → False) := by
  rw [uniqueHoles_iff_occurrences]
  constructor
  · intro u
    refine ⟨fun h a b _ _ ha hb => u h a b ha hb, ?_, ?_⟩
    · intro h x y hx hy
      exact eq_of_heq (Sigma.mk.inj (u h ⟨e, x⟩ ⟨e, y⟩ hx hy)).2
    · rintro h ⟨f, ne, x, hx⟩ ⟨y, hy⟩
      exact ne (congrArg Sigma.fst (u h ⟨f, x⟩ ⟨e, y⟩ hx hy))
  · rintro ⟨away, within, disjoint⟩ h ⟨f, x⟩ ⟨g, y⟩ hx hy
    by_cases fe : f = e
    · subst f
      by_cases ge : g = e
      · subst g
        exact congrArg (Sigma.mk e) (within h x y hx hy)
      · exact False.elim (disjoint h ⟨g, ge, y, hy⟩ ⟨x, hx⟩)
    · by_cases ge : g = e
      · subst g
        exact False.elim (disjoint h ⟨f, fe, x, hx⟩ ⟨y, hy⟩)
      · exact away h ⟨f, x⟩ ⟨g, y⟩ fe ge hx hy

/-- An outer box contributes exactly its body's holes. -/
theorem edgeHasHole_box {d I O} (G : Hypernet ops (d + 1) I O) (e : G.Edge)
    (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b) (h : Hole) :
    EdgeHasHole G e h ↔ HasHole b.body h := by
  unfold EdgeHasHole
  rw [label]
  constructor
  · rintro ⟨x | x, hx⟩
    · cases hx
    · exact ⟨x, hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨.inr x, hx⟩

/-- Split a graph's inventory at any selected edge. -/
theorem hasHole_partition {d I O} (G : Hypernet ops d I O) (e : G.Edge) (h : Hole) :
    HasHole G h ↔ RetainedHole G e h ∨ EdgeHasHole G e h := by
  rw [hasHole_iff_occurrences]
  constructor
  · rintro ⟨⟨f, x⟩, hx⟩
    by_cases eq : f = e
    · subst f; exact .inr ⟨x, hx⟩
    · exact .inl ⟨f, eq, x, hx⟩
  · rintro (⟨f, ne, x, hx⟩ | ⟨x, hx⟩)
    · exact ⟨⟨f, x⟩, hx⟩
    · exact ⟨⟨e, x⟩, hx⟩

/-- Relabelling one box preserves exactly the holes under all other edges. -/
theorem replaceBox_retained_iff {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term)) (h : Hole) :
    RetainedHole (replaceBox G e b label body) e h ↔ RetainedHole G e h := by
  unfold RetainedHole
  have same (f : G.Edge) (ne : f ≠ e) :
      (replaceBox G e b label body).edgeLabel f = G.edgeLabel f := by
    simp [ne]
  constructor
  · rintro ⟨f, ne, x, hx⟩
    exact ⟨f, ne, same f ne ▸ x, (fiberHole_transport (same f ne) x).trans hx⟩
  · rintro ⟨f, ne, x, hx⟩
    exact ⟨f, ne, (same f ne).symm ▸ x, (fiberHole_transport (same f ne).symm x).trans hx⟩

/-- Exact inventory for a change of one box body. -/
theorem replaceBox_hasHole_iff {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term)) (h : Hole) :
    HasHole (replaceBox G e b label body) h ↔ RetainedHole G e h ∨ HasHole body h := by
  rw [hasHole_partition (replaceBox G e b label body) e, replaceBox_retained_iff]
  rw [edgeHasHole_box (replaceBox G e b label body) e ⟨b.bound, b.free, body⟩ (by simp only [↓reduceIte]; rfl)]

/-- A box's fibre is unique exactly when its body is a context. -/
theorem boxFiber_unique_iff {d} (b : Box (alphabet ops d)) :
    (∀ h (x y : Fiber ops (d + 1) (.inr b)),
      fiberHole ops (d + 1) (.inr b) x = some h →
      fiberHole ops (d + 1) (.inr b) y = some h → x = y) ↔
    UniqueHoles ops d b.body := by
  constructor
  · intro u h x y hx hy
    exact Sum.inr.inj (u h (.inr x) (.inr y) hx hy)
  · intro u h x y hx hy
    cases x with
    | inl x => cases hx
    | inr x =>
      cases y with
      | inl y => cases hy
      | inr y => exact congrArg Sum.inr (u h x y hx hy)

/-- Uniqueness in a graph implies uniqueness inside each of its boxes. -/
theorem uniqueHoles_box_body {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (unique : UniqueHoles ops (d + 1) G) : UniqueHoles ops d b.body := by
  have within := ((uniqueHoles_partition G e).mp unique).2.1
  rw [label] at within
  exact (boxFiber_unique_iff b).mp within

/-- The unaffected part remains unique when one box body is changed. -/
theorem replaceBox_awayUnique {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (unique : UniqueHoles ops (d + 1) G) : AwayUnique (replaceBox G e b label body) e := by
  intro h ⟨f, x⟩ ⟨g, y⟩ hf hg hx hy
  have lf : (replaceBox G e b label body).edgeLabel f = G.edgeLabel f := by simp [hf]
  have lg : (replaceBox G e b label body).edgeLabel g = G.edgeLabel g := by simp [hg]
  have eq := (uniqueHoles_iff_occurrences G).mp unique h ⟨f, lf ▸ x⟩ ⟨g, lg ▸ y⟩
    ((fiberHole_transport lf x).trans hx) ((fiberHole_transport lg y).trans hy)
  have fg : f = g := congrArg Sigma.fst eq
  subst g
  have xy := fiber_transport_injective lf (eq_of_heq (Sigma.mk.inj eq).2)
  subst y
  rfl

/-- Changing a box in a context is valid exactly when its new body is unique
and has no hole label in common with the unaffected outer edges. -/
theorem replaceBox_uniqueHoles_iff {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (unique : UniqueHoles ops (d + 1) G) :
    UniqueHoles ops (d + 1) (replaceBox G e b label body) ↔
      UniqueHoles ops d body ∧ (∀ h, RetainedHole G e h → HasHole body h → False) := by
  rw [uniqueHoles_partition (replaceBox G e b label body) e]
  have lbl : (replaceBox G e b label body).edgeLabel e = .inr ⟨b.bound, b.free, body⟩ := by simp only [↓reduceIte]; rfl
  have fibre : (∀ h (x y : Fiber ops (d + 1) ((replaceBox G e b label body).edgeLabel e)),
      fiberHole ops (d + 1) _ x = some h → fiberHole ops (d + 1) _ y = some h → x = y) ↔
      UniqueHoles ops d body := by
    rw [lbl]
    exact boxFiber_unique_iff (ops := ops) ⟨b.bound, b.free, body⟩
  rw [fibre]
  have holes := edgeHasHole_box (replaceBox G e b label body) e ⟨b.bound, b.free, body⟩ lbl
  simp only [holes]
  rw [show (∀ h, RetainedHole (replaceBox G e b label body) e h → HasHole body h → False) ↔
      (∀ h, RetainedHole G e h → HasHole body h → False) from
    ⟨fun u h hh => u h ((replaceBox_retained_iff G e b label body h).mpr hh),
      fun u h hh => u h ((replaceBox_retained_iff G e b label body h).mp hh)⟩]
  exact ⟨fun h => h.2, fun h => ⟨replaceBox_awayUnique G e b label body unique, h⟩⟩

/-- Host holes surviving an addressed replacement, defined solely from the
host and address, independently of the replacement graph or provenance map. -/
def SiteRetainedHole {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (h : Hole) : Prop :=
  match site with
  | .shallow C e => RetainedHole C e h
  | .inside e _ _ inner => RetainedHole _ e h ∨ SiteRetainedHole inner h

/-- The exact deep inventory: all and only retained host holes and inserted holes. -/
theorem plugAt_hasHole_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K) (h : Hole) :
    HasHole (plugAt site H) h ↔ SiteRetainedHole site h ∨ HasHole H h := by
  induction site with
  | shallow C e => exact plug_hasHole_iff C e H h
  | inside e b label inner ih =>
    change HasHole (replaceBox _ e b label (plugAt inner H)) h ↔ _
    rw [replaceBox_hasHole_iff, ih H]
    exact or_assoc.symm

/-- Deep freshness excludes exactly collisions with the syntactically retained host. -/
def SiteFresh {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K) : Prop :=
  ∀ h, SiteRetainedHole site h → HasHole H h → False

/-- Retention never manufactures a host hole. -/
theorem siteRetainedHole_hasHole {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) {h : Hole} (retained : SiteRetainedHole site h) : HasHole G h := by
  induction site with
  | shallow C e => exact (hasHole_partition C e h).mpr (.inl retained)
  | inside e b label inner ih =>
    cases retained with
    | inl outer => exact (hasHole_partition _ e h).mpr (.inl outer)
    | inr nested =>
      apply (hasHole_partition _ e h).mpr
      exact .inr ((edgeHasHole_box _ e b label h).mpr (ih nested))

/-- Uniqueness of a plugged graph forces uniqueness of the entire replacement. -/
theorem plug_uniqueHoles_replacement {d I O} (C : Hypernet ops d I O) (e : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (unique : UniqueHoles ops d (C.plug e H)) : UniqueHoles ops d H :=
  uniqueHoles_of_embedding Sum.inr (fun _ => rfl) (fun _ _ h => Sum.inr.inj h) unique

/-- Exact context criterion at arbitrary depth. Even uniqueness of the
replacement is a necessary conclusion, not an assumed hypothesis. -/
theorem plugAt_uniqueHoles_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (unique : UniqueHoles ops depth G) :
    UniqueHoles ops depth (plugAt site H) ↔ UniqueHoles ops r H ∧ SiteFresh site H := by
  induction site with
  | shallow C e =>
    constructor
    · intro u
      exact ⟨plug_uniqueHoles_replacement C e H u, plug_fresh_necessary C e H u⟩
    · rintro ⟨uh, fresh⟩
      exact plug_uniqueHoles_of_fresh C e H unique uh fresh
  | inside e b label inner ih =>
    have ub := uniqueHoles_box_body _ e b label unique
    change UniqueHoles ops _ (replaceBox _ e b label (plugAt inner H)) ↔ _
    rw [replaceBox_uniqueHoles_iff _ e b label _ unique, ih H ub]
    constructor
    · rintro ⟨⟨uh, fresh⟩, outer⟩
      refine ⟨uh, ?_⟩
      intro h retained hh
      cases retained with
      | inl outside => exact outer h outside ((plugAt_hasHole_iff inner H h).mpr (.inr hh))
      | inr nested => exact fresh h nested hh
    · rintro ⟨uh, fresh⟩
      refine ⟨⟨uh, fun h retained hh => fresh h (.inr retained) hh⟩, ?_⟩
      intro h outside hh
      cases (plugAt_hasHole_iff inner H h).mp hh with
      | inl retained =>
        have separate := ((uniqueHoles_partition _ e).mp unique).2.2
        exact separate h outside ((edgeHasHole_box _ e b label h).mpr
          (siteRetainedHole_hasHole inner retained))
      | inr inserted => exact fresh h (.inl outside) inserted

/-- For contexts, the syntactic freshness condition is necessary and sufficient. -/
theorem plugAt_uniqueHoles_iff_fresh {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (ug : UniqueHoles ops depth G) (uh : UniqueHoles ops r H) :
    UniqueHoles ops depth (plugAt site H) ↔ SiteFresh site H := by
  rw [plugAt_uniqueHoles_iff site H ug]
  exact ⟨And.right, fun fresh => ⟨uh, fresh⟩⟩

/-- Certified deep plugging with exact, address-dependent freshness. -/
noncomputable def Context.plugAtFresh {depth I O} (C : Context ops depth I O) {r J K}
    (site : Site ops C.val r J K) (H : Context ops r J K)
    (fresh : SiteFresh site H.val) : Context ops depth I O :=
  ⟨Linear.plugAt site H.val, (plugAt_uniqueHoles_iff_fresh site H.val C.property H.property).mpr fresh⟩

/-- The result is hole-free exactly when neither the retained host nor the
replacement contains a hole; discarded subgraphs are irrelevant. -/
theorem plugAt_holeFree_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K) :
    HoleFree (plugAt site H) ↔ (∀ h, ¬ SiteRetainedHole site h) ∧ HoleFree H := by
  constructor
  · intro free
    exact ⟨fun h retained => free h ((plugAt_hasHole_iff site H h).mpr (.inl retained)),
      fun h inserted => free h ((plugAt_hasHole_iff site H h).mpr (.inr inserted))⟩
  · rintro ⟨retained, inserted⟩ h hh
    exact ((plugAt_hasHole_iff site H h).mp hh).elim (retained h) (inserted h)

/-- Read the selected edge's own hole label, ignoring any descendants. -/
def Site.selectedHole {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) : Option Hole :=
  match site with
  | @Site.shallow _ _ d _ _ C e => shallowHole ops d (C.edgeLabel e)
  | .inside e b label inner => Site.selectedHole inner

/-- A hole selected by an address occurs in the original host. -/
theorem Site.selectedHole_present {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) {h} (selected : site.selectedHole = some h) : HasHole G h := by
  induction site with
  | shallow C e =>
    exact (hasHole_iff_occurrences C h).mpr ⟨⟨e, .inl ()⟩, selected⟩
  | inside e b label inner ih =>
    exact (hasHole_partition _ e h).mpr (.inr ((edgeHasHole_box _ e b label h).mpr (ih selected)))

/-- A context cannot retain another occurrence of the consumed hole label,
regardless of the selected edge's nesting depth. -/
theorem site_selected_not_retained {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (unique : UniqueHoles ops depth G) {h}
    (selected : site.selectedHole = some h) : ¬ SiteRetainedHole site h := by
  induction site with
  | shallow C e => exact removed_hole_not_retained C e unique h selected
  | inside e b label inner ih =>
    intro retained
    cases retained with
    | inl outside =>
      exact ((uniqueHoles_partition _ e).mp unique).2.2 h outside
        ((edgeHasHole_box _ e b label h).mpr (inner.selectedHole_present selected))
    | inr nested => exact ih (uniqueHoles_box_body _ e b label unique) selected nested

/-- A consumed label survives deep plugging precisely when it is reintroduced. -/
theorem plugAt_consumed_hole_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (unique : UniqueHoles ops depth G) {h} (selected : site.selectedHole = some h) :
    HasHole (plugAt site H) h ↔ HasHole H h := by
  rw [plugAt_hasHole_iff]
  exact or_iff_right (site_selected_not_retained site unique selected)

end Hypernets.Linear

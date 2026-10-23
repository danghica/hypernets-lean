import Hypernets.Graph.TransportPlug
import Hypernets.Graph.RecursiveIsoPlug

/-! Occurrence addresses and substitution are invariant under host renaming. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Transport the interface indices of an address along equalities. -/
def Site.reinterface {d I O} {G : Hypernet ops d I O} {r J K J' K'}
    (s : Site ops G r J K) (hi : J = J') (ho : K = K') : Site ops G r J' K' :=
  hi ▸ ho ▸ s

/-- Address transport agrees with transporting the replacement interface back. -/
theorem plugAt_reinterface {d I O} {G : Hypernet ops d I O} {r J K J' K'}
    (s : Site ops G r J K) (hi : J = J') (ho : K = K') (H : Hypernet ops r J' K') :
    plugAt (s.reinterface hi ho) H = plugAt s (H.reboundary hi.symm ho.symm) := by
  cases hi; cases ho; simp [Site.reinterface]

/-- A box at a selected edge is carried to a box with the same binding and free
interface and a recursively isomorphic body. -/
theorem DeepIso.boxAt {d I O} {G H : Hypernet ops (d + 1) I O}
    (f : DeepIso G H) (e : G.Edge) (b : Box (alphabet ops d))
    (label : G.edgeLabel e = .inr b) :
    ∃ body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term),
      H.edgeLabel (f.edges.toFun e) = .inr ⟨b.bound, b.free, body⟩ ∧
      Nonempty (DeepIso b.body body) := by
  have rel := f.edge_label e
  rw [label] at rel
  cases ht : H.edgeLabel (f.edges.toFun e) with
  | inl p => simp [ht, LabelEquiv] at rel
  | inr c =>
      rw [ht] at rel
      change BoxRelated _ _ b c at rel
      cases rel with
      | bodies related => exact ⟨_, rfl, related⟩

/-- Replace corresponding boxes in isomorphic hosts by isomorphic new bodies. -/
noncomputable def DeepIso.replaceBox {d I O} {G H : Hypernet ops (d + 1) I O}
    (f : DeepIso G H) (e : G.Edge) (b : Box (alphabet ops d))
    (label : G.edgeLabel e = .inr b)
    (old : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (label' : H.edgeLabel (f.edges.toFun e) = .inr ⟨b.bound, b.free, old⟩)
    {A B : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term)}
    (g : DeepIso A B) :
    DeepIso (Linear.replaceBox G e b label A)
      (Linear.replaceBox H (f.edges.toFun e) ⟨b.bound, b.free, old⟩ label' B) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label x := by
    classical
    by_cases hx : x = e
    · subst x
      simp only [Linear.replaceBox, Net.relabelEdges, ↓reduceIte]
      exact BoxRelated.bodies ⟨g⟩
    · have hy : f.edges.toFun x ≠ f.edges.toFun e := fun h => hx (f.edges.injective h)
      change LabelEquiv ops (d + 1)
        (if x = e then .inr ⟨b.bound, b.free, A⟩ else G.edgeLabel x)
        (if f.edges.toFun x = f.edges.toFun e then .inr ⟨b.bound, b.free, B⟩
          else H.edgeLabel (f.edges.toFun x))
      simp only [alphabet, nextAlphabet, ite_eq_right hx, ite_eq_right hy]
      exact f.edge_label x
  source := f.source
  target := f.target

/-- Structural correspondence of occurrence addresses: follow the host edge
bijection at each level, descending through corresponding boxes. -/
inductive SiteIso : {d : Nat} → {I O : List Wire} →
    {G H : Hypernet ops d I O} → {r : Nat} → {J K : List Wire} →
    Site ops G r J K → Site ops H r J K → Prop where
  | shallow {d I O} {G H : Hypernet ops d I O} (f : DeepIso G H) (e : G.Edge) :
      SiteIso (.shallow G e)
        ((Site.shallow H (f.edges.toFun e)).reinterface
          (labelEquiv_input ops d (f.edge_label e)).symm
          (labelEquiv_output ops d (f.edge_label e)).symm)
  | inside {d I O} {G H : Hypernet ops (d + 1) I O} (f : DeepIso G H)
      (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
      (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
      (label' : H.edgeLabel (f.edges.toFun e) = .inr ⟨b.bound, b.free, body⟩)
      {r J K} {s : Site ops b.body r J K} {t : Site ops body r J K}
      (inner : SiteIso s t) :
      SiteIso (.inside e b label s)
        (.inside (f.edges.toFun e) ⟨b.bound, b.free, body⟩ label' t)

/-- Every addressed occurrence can be transported along a recursive host isomorphism. -/
theorem Site.transport_exists {d I O} {G H : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) (f : DeepIso G H) : ∃ t : Site ops H r J K, SiteIso s t := by
  induction s with
  | shallow G e => exact ⟨_, SiteIso.shallow f e⟩
  | inside e b label inner ih =>
      obtain ⟨body, label', ⟨g⟩⟩ := f.boxAt e b label
      obtain ⟨t, ht⟩ := ih g
      exact ⟨_, SiteIso.inside f e b label body label' ht⟩

/-- Choose a structurally corresponding occurrence in the renamed host. -/
noncomputable def Site.transport {d I O} {G H : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) (f : DeepIso G H) : Site ops H r J K :=
  Classical.choose (s.transport_exists f)

/-- The chosen address follows corresponding edges and boxes. -/
theorem Site.transport_spec {d I O} {G H : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) (f : DeepIso G H) : SiteIso s (s.transport f) :=
  Classical.choose_spec (s.transport_exists f)

/-- Plugging at structurally corresponding sites preserves recursive isomorphism. -/
theorem SiteIso.plug {d I O} {G H : Hypernet ops d I O} {r J K}
    {s : Site ops G r J K} {t : Site ops H r J K} (h : SiteIso s t)
    (A : Hypernet ops r J K) : Nonempty (DeepIso (plugAt s A) (plugAt t A)) := by
  induction h with
  | shallow f e =>
      rw [plugAt_reinterface]
      exact ⟨f.plugHost e (labelEquiv_input ops _ (f.edge_label e))
        (labelEquiv_output ops _ (f.edge_label e)) (labelEquiv_refl ops _) A⟩
  | inside f e b label body label' inner ih =>
      obtain ⟨g⟩ := ih A
      exact ⟨f.replaceBox e b label body label' g⟩

/-- Simultaneous congruence in the host address and the replacement. -/
theorem SiteIso.plug_congr {d I O} {G H : Hypernet ops d I O} {r J K}
    {s : Site ops G r J K} {t : Site ops H r J K} (h : SiteIso s t)
    {A B : Hypernet ops r J K} (g : DeepIso A B) :
    Nonempty (DeepIso (plugAt s A) (plugAt t B)) := by
  obtain ⟨f⟩ := h.plug A
  exact ⟨f.trans (plugAt_deepIso t g)⟩

/-- The quotient result is independent of a simultaneous renaming of host and replacement. -/
theorem plugAtModuloIso_transport {d I O} {G H : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) (f : DeepIso G H) (A : HypernetModuloIso ops r J K) :
    plugAtModuloIso s A = plugAtModuloIso (s.transport f) A := by
  induction A using Quotient.inductionOn with
  | h A => exact Quotient.sound ((s.transport_spec f).plug A)

/-- Host renaming preserves the holes outside the selected outer edge. -/
theorem DeepIso.retainedHole_iff {d I O} {G H : Hypernet ops d I O}
    (f : DeepIso G H) (e : G.Edge) (h : Hole) :
    RetainedHole G e h ↔ RetainedHole H (f.edges.toFun e) h := by
  constructor
  · rintro ⟨x, hx, a, ha⟩
    let emb := labelEquiv_embedding ops d (f.edge_label x)
    exact ⟨f.edges.toFun x, fun eq => hx (f.edges.injective eq), emb.map a,
      (emb.hole a).trans ha⟩
  · rintro ⟨y, hy, a, ha⟩
    let emb := labelEquiv_embedding ops d ((DeepIso.symm f).edge_label y)
    refine ⟨f.edges.invFun y, ?_, emb.map a, (emb.hole a).trans ha⟩
    intro eq
    exact hy (by rw [← f.edges.right_inv y, eq])

/-- Changing only interface equality proofs does not change retained holes. -/
theorem SiteRetainedHole_reinterface {d I O} {G : Hypernet ops d I O} {r J K J' K'}
    (s : Site ops G r J K) (hi : J = J') (ho : K = K') (h : Hole) :
    SiteRetainedHole (s.reinterface hi ho) h ↔ SiteRetainedHole s h := by
  cases hi; cases ho; rfl

/-- Corresponding addresses retain exactly the same hole labels. -/
theorem SiteIso.retainedHole_iff {d I O} {G H : Hypernet ops d I O} {r J K}
    {s : Site ops G r J K} {t : Site ops H r J K} (iso : SiteIso s t) (h : Hole) :
    SiteRetainedHole s h ↔ SiteRetainedHole t h := by
  induction iso with
  | shallow f e =>
      rw [SiteRetainedHole_reinterface]
      exact f.retainedHole_iff e h
  | inside f e b label body label' inner ih =>
      exact or_congr (f.retainedHole_iff e h) ih

/-- Exact freshness is invariant under simultaneous host and replacement renaming. -/
theorem SiteIso.fresh_iff {d I O} {G H : Hypernet ops d I O} {r J K}
    {s : Site ops G r J K} {t : Site ops H r J K} (iso : SiteIso s t)
    {A B : Hypernet ops r J K} (f : DeepIso A B) : SiteFresh s A ↔ SiteFresh t B :=
  ⟨fun fresh h retained inserted => fresh h ((iso.retainedHole_iff h).mpr retained)
      ((DeepIso.hasHole_iff f h).mpr inserted),
    fun fresh h retained inserted => fresh h ((iso.retainedHole_iff h).mp retained)
      ((DeepIso.hasHole_iff f h).mp inserted)⟩

/-- Context validity of the result is independent of both sets of carrier names. -/
theorem SiteIso.plug_unique_iff {d I O} {G H : Hypernet ops d I O} {r J K}
    {s : Site ops G r J K} {t : Site ops H r J K} (iso : SiteIso s t)
    {A B : Hypernet ops r J K} (f : DeepIso A B) :
    UniqueHoles ops d (plugAt s A) ↔ UniqueHoles ops d (plugAt t B) := by
  obtain ⟨g⟩ := iso.plug_congr f
  exact DeepIso.uniqueHoles_iff g

end Hypernets.Linear

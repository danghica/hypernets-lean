import Hypernets.Graph.PlugAssociativity
import Hypernets.Graph.SiteTransport

/-! Composition of arbitrary-depth occurrence sites and associativity of substitution. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Replacing a selected box twice leaves precisely the last body. -/
theorem replaceBox_overwrite {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    (A B : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (label' : (replaceBox G e b label A).edgeLabel e = .inr ⟨b.bound, b.free, A⟩) :
    replaceBox (replaceBox G e b label A) e ⟨b.bound, b.free, A⟩ label' B =
      replaceBox G e b label B := by
  classical
  simp only [replaceBox, Net.relabelEdges]
  congr 1
  funext x
  by_cases h : x = e <;> simp [alphabet, nextAlphabet, h]

/-- Changing the body of an inserted box commutes with shallow insertion. -/
noncomputable def plug_replaceBox_iso {d I O} (C : Hypernet ops (d + 1) I O) (e : C.Edge)
    (H : Hypernet ops (d + 1) ((alphabet ops (d + 1)).signature.input (C.edgeLabel e))
      ((alphabet ops (d + 1)).signature.output (C.edgeLabel e)))
    (f : H.Edge) (b : Box (alphabet ops d)) (label : H.edgeLabel f = .inr b)
    (A : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term)) :
    Net.Iso (replaceBox (C.plug e H) (.inr f) b label A)
      (C.plug e (replaceBox H f b label A)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label x := by
    classical
    cases x with
    | inl x => simp [replaceBox, Net.relabelEdges, Net.plug, Net.Replacement.edgeLabel, Bijection.refl]
    | inr x =>
      simp [Net.plug, Net.Replacement.edgeLabel, replaceBox, Net.relabelEdges, Bijection.refl]
  source x := by
    cases x with
    | inl x => simp [Net.plug, Net.Replacement.source, Bijection.refl, Net.Replacement.host]
    | inr x =>
      change ((H.source x).map (Net.Replacement.insert C e H)).map (Port.map id) =
        (H.source x).map (Net.Replacement.insert C e (replaceBox H f b label A))
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      dsimp only [Function.comp_def]
      rw [Port.map_id]
      cases v <;> rfl
  target x := by
    cases x with
    | inl x => simp [Net.plug, Net.Replacement.target, Bijection.refl, Net.Replacement.host]
    | inr x =>
      change ((H.target x).map (Net.Replacement.insert C e H)).map (Port.map id) =
        (H.target x).map (Net.Replacement.insert C e (replaceBox H f b label A))
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      dsimp only [Function.comp_def]
      rw [Port.map_id]
      cases v <;> rfl

/-- After inserting a graph at an outer site, locate an inner site of that graph
in the result. The address follows constructors directly, without choosing an isomorphism. -/
noncomputable def Site.comp {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) : Site ops (plugAt s H) q U V := by
  classical
  induction s with
  | shallow C e =>
      cases t with
      | shallow H f => exact .shallow (C.plug e H) (.inr f)
      | inside f b label inner => exact .inside (G := C.plug e H) (.inr f) b label inner
  | inside e b label inner ih =>
      exact .inside (G := plugAt (.inside e b label inner) H) e ⟨b.bound, b.free, plugAt inner H⟩
        (by simp [plugAt, replaceBox, Net.relabelEdges, alphabet, nextAlphabet]) (ih t)

/-- Arbitrary nested substitutions associate up to recursive isomorphism. -/
noncomputable def plugAt_assoc {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (A : Hypernet ops q U V) :
    DeepIso (plugAt (s.comp t) A) (plugAt s (plugAt t A)) := by
  induction s with
  | shallow C e =>
      cases t with
      | shallow H f => exact DeepIso.ofIso (C.plug_assoc e H f A)
      | inside f b label inner => exact DeepIso.ofIso (plug_replaceBox_iso C e _ f b label (plugAt inner A))
  | inside e b label inner ih =>
      change DeepIso (replaceBox (replaceBox _ e b label (plugAt inner H)) e
        ⟨b.bound, b.free, plugAt inner H⟩
        (by simp [alphabet, nextAlphabet]) (plugAt (inner.comp t) A)) _
      rw [replaceBox_overwrite]
      exact replaceBox_deepIso _ e b label (ih t)

/-- On recursive isomorphism classes, nested substitution is actual equality. -/
theorem plugAtModuloIso_comp {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (A : HypernetModuloIso ops q U V) :
    plugAtModuloIso (s.comp t) A = plugAtModuloIso s (plugAtModuloIso t A) := by
  induction A using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨plugAt_assoc s t A⟩

/-- The final selected label comes from the inner address. -/
theorem Site.selectedHole_comp {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) : (s.comp t).selectedHole = t.selectedHole := by
  induction s with
  | shallow C e => cases t <;> rfl
  | inside e b label inner ih => exact ih t

/-- Removing an inserted edge retains exactly the surviving host fibres and
all middle-graph fibres except the selected one. -/
theorem retainedHole_inserted {d I O} (C : Hypernet ops d I O) (e : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) (f : H.Edge) (h : Hole) :
    RetainedHole (C.plug e H) (.inr f) h ↔ RetainedHole C e h ∨ RetainedHole H f h := by
  constructor
  · rintro ⟨x | y, ne, a, ha⟩
    · exact .inl ⟨x.val, x.property, a, ha⟩
    · exact .inr ⟨y, fun eq => ne (congrArg Sum.inr eq), a, ha⟩
  · rintro (⟨x, ne, a, ha⟩ | ⟨y, ne, a, ha⟩)
    · exact ⟨.inl ⟨x, ne⟩, (by intro eq; cases eq), a, ha⟩
    · exact ⟨.inr y, fun eq => ne (Sum.inr.inj eq), a, ha⟩

/-- A composed address retains the union of the two original retained inventories. -/
theorem siteRetainedHole_comp {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (h : Hole) :
    SiteRetainedHole (s.comp t) h ↔ SiteRetainedHole s h ∨ SiteRetainedHole t h := by
  induction s with
  | shallow C e =>
      cases t with
      | shallow H f => exact retainedHole_inserted C e H f h
      | inside f b label inner =>
          change (RetainedHole (C.plug e _) (.inr f) h ∨ SiteRetainedHole inner h) ↔ _
          rw [retainedHole_inserted]
          exact or_assoc
  | inside e b label inner ih =>
      change (RetainedHole (replaceBox _ e b label (plugAt inner H)) e h ∨
        SiteRetainedHole (inner.comp t) h) ↔ _
      rw [replaceBox_retained_iff, ih t]
      exact or_assoc.symm

/-- The exact final hole inventory consists of both retained inventories and
the final replacement, irrespective of the order of the two substitutions. -/
theorem plugAt_comp_hasHole_iff {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (A : Hypernet ops q U V) (h : Hole) :
    HasHole (plugAt (s.comp t) A) h ↔
      SiteRetainedHole s h ∨ SiteRetainedHole t h ∨ HasHole A h := by
  rw [plugAt_hasHole_iff, siteRetainedHole_comp]
  exact or_assoc

/-- Exact freshness of a composed address separates into the two retained sets. -/
theorem siteFresh_comp_iff {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (A : Hypernet ops q U V) :
    SiteFresh (s.comp t) A ↔
      (∀ h, SiteRetainedHole s h → HasHole A h → False) ∧ SiteFresh t A := by
  constructor
  · intro fresh
    exact ⟨fun h retained present => fresh h ((siteRetainedHole_comp s t h).mpr (.inl retained)) present,
      fun h retained present => fresh h ((siteRetainedHole_comp s t h).mpr (.inr retained)) present⟩
  · rintro ⟨outer, inner⟩ h retained present
    rcases (siteRetainedHole_comp s t h).mp retained with retained | retained
    · exact outer h retained present
    · exact inner h retained present

/-- Sharp context closure for composed substitution: final unique holes and
pairwise disjointness of the two retained inventories and the final replacement.
The intermediate plugged graph need not itself have unique holes. -/
theorem plugAt_comp_unique_iff {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) (A : Hypernet ops q U V)
    (ug : UniqueHoles ops d G) (uh : UniqueHoles ops r H) :
    UniqueHoles ops d (plugAt (s.comp t) A) ↔
      UniqueHoles ops q A ∧ SiteFresh (s.comp t) A ∧
        (∀ h, SiteRetainedHole s h → SiteRetainedHole t h → False) := by
  rw [DeepIso.uniqueHoles_iff (plugAt_assoc s t A), plugAt_uniqueHoles_iff s _ ug,
    plugAt_uniqueHoles_iff t A uh, siteFresh_comp_iff]
  constructor
  · rintro ⟨⟨ua, ft⟩, fs⟩
    exact ⟨ua, ⟨fun h hs ha => fs h hs ((plugAt_hasHole_iff t A h).mpr (.inr ha)), ft⟩,
      fun h hs ht => fs h hs ((plugAt_hasHole_iff t A h).mpr (.inl ht))⟩
  · rintro ⟨ua, ⟨fs, ft⟩, disjoint⟩
    refine ⟨⟨ua, ft⟩, ?_⟩
    intro h hs present
    rcases (plugAt_hasHole_iff t A h).mp present with ht | ha
    · exact disjoint h hs ht
    · exact fs h hs ha

/-- Package composed substitution as a context using the sharp final criterion,
without requiring the intermediate graph to be a context. -/
noncomputable def Context.plugAtComp {d I O} (G : Context ops d I O) {r J K}
    (s : Site ops G.val r J K) (H : Context ops r J K) {q U V}
    (t : Site ops H.val q U V) (A : Context ops q U V)
    (fresh : SiteFresh (s.comp t) A.val)
    (disjoint : ∀ h, SiteRetainedHole s h → SiteRetainedHole t h → False) : Context ops d I O :=
  ⟨Linear.plugAt (s.comp t) A.val,
    (plugAt_comp_unique_iff s t A.val G.property H.property).mpr ⟨A.property, fresh, disjoint⟩⟩

/-- Three nested substitutions give the same quotient operation under either
bracketing of site composition; no equality of carrier records is required. -/
theorem plugAtModuloIso_comp_three {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) {H : Hypernet ops r J K} {q U V}
    (t : Site ops H q U V) {A : Hypernet ops q U V} {p X Y}
    (u : Site ops A p X Y) (B : HypernetModuloIso ops p X Y) :
    plugAtModuloIso ((s.comp t).comp u) B = plugAtModuloIso (s.comp (t.comp u)) B := by
  rw [plugAtModuloIso_comp, plugAtModuloIso_comp, plugAtModuloIso_comp, plugAtModuloIso_comp]

end Hypernets.Linear

import Hypernets.Graph.RelIsoPlug
import Hypernets.Graph.RecursiveIsoHoles

/-! Substitution respects recursive isomorphism at every addressed depth. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Boxes containing recursively isomorphic bodies are recursively isomorphic. -/
def DeepIso.box {d bound free}
    {G H : Hypernet ops d [.term] (List.replicate (bound + free) .term)}
    (f : DeepIso G H) : DeepIso (box (bound := bound) (free := free) G)
      (box (bound := bound) (free := free) H) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := nomatch v
  edge_label _ := .bodies ⟨f⟩
  source _ := by simp [Linear.box, Net.corolla, Bijection.refl, nextAlphabet]
  target _ := by simp [Linear.box, Net.corolla, Bijection.refl, nextAlphabet]

/-- Changing the same box to recursively isomorphic bodies preserves recursive
isomorphism of the surrounding graph. All outer names remain fixed. -/
noncomputable def replaceBox_deepIso {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b)
    {H K : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term)}
    (f : DeepIso H K) : DeepIso (replaceBox G e b label H) (replaceBox G e b label K) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label x := by
    classical
    by_cases eq : x = e
    · subst x
      simp only [replaceBox, Net.relabelEdges, Bijection.refl, id_eq, ↓reduceIte]
      exact BoxRelated.bodies ⟨f⟩
    · change LabelEquiv ops (d + 1)
        (if x = e then .inr ⟨b.bound, b.free, H⟩ else G.edgeLabel x)
        (if x = e then .inr ⟨b.bound, b.free, K⟩ else G.edgeLabel x)
      simp only [alphabet, nextAlphabet, ite_eq_right eq]
      exact labelEquiv_refl ops (d + 1) _
  source x := by change (G.source x).map (Port.map id) = G.source x; simp
  target x := by change (G.target x).map (Port.map id) = G.target x; simp

/-- Isomorphic replacements produce isomorphic results in every fixed addressed
context, including replacement inside any finite number of enclosing boxes. -/
noncomputable def plugAt_deepIso {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) {H K' : Hypernet ops r J K} (f : DeepIso H K') :
    DeepIso (plugAt site H) (plugAt site K') := by
  induction site with
  | shallow C e => exact Net.RelIso.plug C e (labelEquiv_refl ops _) f
  | inside e b label inner ih => exact replaceBox_deepIso _ e b label (ih f)

/-- Exact freshness depends on the replacement's isomorphism class, not its names. -/
theorem siteFresh_deepIso_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) {H K' : Hypernet ops r J K} (f : DeepIso H K') :
    SiteFresh site H ↔ SiteFresh site K' :=
  ⟨fun fresh h retained inserted => fresh h retained ((DeepIso.hasHole_iff f h).mpr inserted),
    fun fresh h retained inserted => fresh h retained ((DeepIso.hasHole_iff f h).mp inserted)⟩

/-- The context property of the result is independent of all replacement carrier names. -/
theorem plugAt_deepIso_unique_iff {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) {H K' : Hypernet ops r J K} (f : DeepIso H K') :
    UniqueHoles ops depth (plugAt site H) ↔ UniqueHoles ops depth (plugAt site K') :=
  DeepIso.uniqueHoles_iff (plugAt_deepIso site f)

/-- Recursive isomorphism gives an equivalence relation on each typed depth layer. -/
def deepSetoid (ops : Operations Op) (d : Nat) (I O : List Wire) : Setoid (Hypernet ops d I O) where
  r G H := Nonempty (DeepIso G H)
  iseqv := {
    refl G := ⟨DeepIso.refl G⟩
    symm := fun ⟨f⟩ => ⟨DeepIso.symm f⟩
    trans := fun ⟨f⟩ ⟨g⟩ => ⟨DeepIso.trans f g⟩
  }

/-- A hypernet modulo independent renaming at every level of its hierarchy. -/
abbrev HypernetModuloIso (ops : Operations Op) (d : Nat) (I O : List Wire) :=
  Quotient (deepSetoid ops d I O)

/-- For a fixed host and site, plugging is well-defined on replacement
isomorphism classes and returns an isomorphism class of whole graphs. -/
noncomputable def plugAtModuloIso {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) : HypernetModuloIso ops r J K → HypernetModuloIso ops depth I O :=
  Quotient.lift (fun H => Quotient.mk (deepSetoid ops depth I O) (plugAt site H))
    (by rintro H K' ⟨f⟩; exact Quotient.sound ⟨plugAt_deepIso site f⟩)

/-- The quotient operation agrees with concrete replacement on representatives. -/
theorem plugAtModuloIso_mk {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K) :
    plugAtModuloIso site (Quotient.mk (deepSetoid ops r J K) H) =
      Quotient.mk (deepSetoid ops depth I O) (plugAt site H) := rfl

/-- Context validity is a well-defined predicate on recursive isomorphism classes. -/
def moduloIsoUniqueHoles {d I O} : HypernetModuloIso ops d I O → Prop :=
  Quotient.lift (UniqueHoles ops d) (by rintro G H ⟨f⟩; exact propext (DeepIso.uniqueHoles_iff f))

end Hypernets.Linear

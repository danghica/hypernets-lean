import Hypernets.Graph.PlugUnits
import Hypernets.Graph.DeepAssociativity

/-! Restoration at deep sites and the unit law on recursive isomorphism classes. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- The one-edge fragment carrying the original selected label, including its
entire box body when the selected occurrence itself is a box. -/
noncomputable def Site.original {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) : Hypernet ops r J K := by
  induction s with
  | shallow C e => exact Net.corolla _ (C.edgeLabel e)
  | inside e b label inner ih => exact ih

/-- Reinstalling the original body of a selected box preserves its host. -/
noncomputable def replaceBox_original_iso {d I O} (G : Hypernet ops (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops d)) (label : G.edgeLabel e = .inr b) :
    Net.Iso (replaceBox G e b label b.body) G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label x := by
    classical
    by_cases h : x = e
    · subst x
      change G.edgeLabel e = if e = e then .inr ⟨b.bound, b.free, b.body⟩ else G.edgeLabel e
      simpa only [↓reduceIte] using label
    · change G.edgeLabel x = if x = e then .inr ⟨b.bound, b.free, b.body⟩ else G.edgeLabel x
      simp only [alphabet, nextAlphabet, ite_eq_right h]
  source x := by change (G.source x).map (Port.map id) = G.source x; simp
  target x := by change (G.target x).map (Port.map id) = G.target x; simp

/-- Substituting the original selected fragment restores the entire host up to
recursive isomorphism, at every nesting depth. -/
noncomputable def plugAt_original {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) : DeepIso (plugAt s s.original) G := by
  induction s with
  | shallow C e => exact DeepIso.ofIso (C.plug_corolla_iso e)
  | inside e b label inner ih =>
      exact (replaceBox_deepIso _ e b label ih).trans
        (DeepIso.ofIso (replaceBox_original_iso _ e b label))

/-- The original host and its restored representative have equal quotient classes. -/
theorem plugAtModuloIso_original {d I O} {G : Hypernet ops d I O} {r J K}
    (s : Site ops G r J K) :
    plugAtModuloIso s (Quotient.mk (deepSetoid ops r J K) s.original) =
      Quotient.mk (deepSetoid ops d I O) G := Quotient.sound ⟨plugAt_original s⟩

/-- Every one-edge substitution context acts identically on replacement classes. -/
theorem plugAtModuloIso_corolla {d} (o : (alphabet ops d).Symbol)
    (A : HypernetModuloIso ops d ((alphabet ops d).signature.input o)
      ((alphabet ops d).signature.output o)) :
    plugAtModuloIso (.shallow (Net.corolla (alphabet ops d).signature o) 0) A = A := by
  induction A using Quotient.inductionOn with
  | h A => exact Quotient.sound ⟨DeepIso.ofIso (Net.corolla_plug_iso o A)⟩

end Hypernets.Linear

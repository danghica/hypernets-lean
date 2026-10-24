import Hypernets.Graph.BoxInterchange

/-! Constructive residual addresses and interchange at independent deep sites. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Structural independence: addresses diverge at distinct edges, possibly
after a common chain of enclosing boxes. An ancestor and descendant are excluded. -/
inductive IndependentSites : {d : Nat} → {I O : List Wire} →
    {C : Hypernet ops d I O} → {r : Nat} → {J K : List Wire} →
    {q : Nat} → {U V : List Wire} → Site ops C r J K → Site ops C q U V → Type 1 where
  | shallow {d I O} (C : Hypernet ops d I O) (e f : C.Edge) (ne : f ≠ e) :
      IndependentSites (.shallow C e) (.shallow C f)
  | shallow_inside {d I O} (C : Hypernet ops (d+1) I O) (e f : C.Edge) (ne : f ≠ e)
      (b : Box (alphabet ops d)) (label : C.edgeLabel f = .inr b) {q U V}
      (t : Site ops b.body q U V) :
      IndependentSites (.shallow C e) (.inside f b label t)
  | separate_boxes {d I O} (C : Hypernet ops (d+1) I O) (e f : C.Edge) (ne : f ≠ e)
      (b c : Box (alphabet ops d)) (le : C.edgeLabel e = .inr b) (lf : C.edgeLabel f = .inr c)
      {r J K q U V} (s : Site ops b.body r J K) (t : Site ops c.body q U V) :
      IndependentSites (.inside e b le s) (.inside f c lf t)
  | same_box {d I O} (C : Hypernet ops (d+1) I O) (e : C.Edge)
      (b : Box (alphabet ops d)) (label : C.edgeLabel e = .inr b)
      {r J K q U V} {s : Site ops b.body r J K} {t : Site ops b.body q U V}
      (inner : IndependentSites s t) :
      IndependentSites (.inside e b label s) (.inside e b label t)
  | swap {d I O} {C : Hypernet ops d I O} {r J K q U V}
      {s : Site ops C r J K} {t : Site ops C q U V} (h : IndependentSites s t) :
      IndependentSites t s

/-- Residual sites and the isomorphism comparing the two orders. The sites
are built from retained occurrences, not inferred from equality of results. -/
structure InterchangeResult {d I O} {C : Hypernet ops d I O} {r J K q U V}
    (s : Site ops C r J K) (t : Site ops C q U V)
    (A : Hypernet ops r J K) (B : Hypernet ops q U V) where
  rightAfterLeft : Site ops (plugAt s A) q U V
  leftAfterRight : Site ops (plugAt t B) r J K
  iso : DeepIso (plugAt rightAfterLeft B) (plugAt leftAfterRight A)

/-- Independent substitutions commute at arbitrary depth, with explicitly
constructed residual occurrences in both intermediate graphs. -/
noncomputable def IndependentSites.interchange {d I O} {C : Hypernet ops d I O}
    {r J K q U V} {s : Site ops C r J K} {t : Site ops C q U V}
    (h : IndependentSites s t) (A : Hypernet ops r J K) (B : Hypernet ops q U V) :
    InterchangeResult s t A B := by
  classical
  induction h with
  | shallow C e f ne =>
      exact ⟨.shallow (C.plug e A) (.inl ⟨f,ne⟩),
        .shallow (C.plug f B) (.inl ⟨e,Ne.symm ne⟩),
        DeepIso.ofIso (Net.PlugInterchange.iso C e f ne A B)⟩
  | shallow_inside C e f ne b label t =>
      exact ⟨.inside (G := C.plug e A) (.inl ⟨f,ne⟩) b label t,
        Site.afterBox C e f (Ne.symm ne) b label (plugAt t B),
        DeepIso.ofIso (plug_retained_box_iso C e f ne b label A (plugAt t B))⟩
  | separate_boxes C e f ne b c le lf s t =>
      exact ⟨.inside (G := replaceBox C e b le (plugAt s A)) f c
          ((replaceBox_other_label C e b le (plugAt s A) f ne).trans lf) t,
        .inside (G := replaceBox C f c lf (plugAt t B)) e b
          ((replaceBox_other_label C f c lf (plugAt t B) e (Ne.symm ne)).trans le) s,
        by
          dsimp only [plugAt]
          rw [replaceBox_comm C e f ne b c le lf]
          exact DeepIso.refl _⟩
  | same_box C e b label inner ih =>
      let result := ih A B
      refine ⟨.inside (G := replaceBox C e b label (plugAt _ A)) e
        ⟨b.bound,b.free,plugAt _ A⟩ (by simp [alphabet,nextAlphabet])
        result.rightAfterLeft,
        .inside (G := replaceBox C e b label (plugAt _ B)) e
        ⟨b.bound,b.free,plugAt _ B⟩ (by simp [alphabet,nextAlphabet])
        result.leftAfterRight, ?_⟩
      dsimp only [plugAt]
      rw [replaceBox_overwrite,replaceBox_overwrite]
      exact replaceBox_deepIso C e b label result.iso
  | swap h ih =>
      let result := ih B A
      exact ⟨result.leftAfterRight,result.rightAfterLeft,result.iso.symm⟩

/-- Interface equality transport does not change the selected hole label. -/
theorem Site.selectedHole_reinterface {d I O} {C : Hypernet ops d I O} {r J K J' K'}
    (s : Site ops C r J K) (hi : J = J') (ho : K = K') :
    (s.reinterface hi ho).selectedHole = s.selectedHole := by
  cases hi; cases ho; rfl

/-- Both residual addresses still select the original hole labels. -/
theorem IndependentSites.residual_selectedHole {d I O} {C : Hypernet ops d I O}
    {r J K q U V} {s : Site ops C r J K} {t : Site ops C q U V}
    (h : IndependentSites s t) (A : Hypernet ops r J K) (B : Hypernet ops q U V) :
    (h.interchange A B).rightAfterLeft.selectedHole = t.selectedHole ∧
      (h.interchange A B).leftAfterRight.selectedHole = s.selectedHole := by
  induction h with
  | shallow C e f ne => exact ⟨rfl,rfl⟩
  | shallow_inside C e f ne b label t =>
      refine ⟨rfl,?_⟩
      change (Site.afterBox C e f (Ne.symm ne) b label (plugAt t B)).selectedHole = _
      rw [Site.afterBox,Site.selectedHole_reinterface]
      change shallowHole ops _ ((replaceBox C f b label (plugAt t B)).edgeLabel e) = _
      rw [replaceBox_other_label C f b label (plugAt t B) e (Ne.symm ne)]
      rfl
  | separate_boxes => exact ⟨rfl,rfl⟩
  | same_box C e b label inner ih => exact ih A B
  | swap h ih => exact (ih B A).symm

/-- Interchange is literal equality of final recursive graph classes. -/
theorem IndependentSites.interchange_modulo {d I O} {C : Hypernet ops d I O}
    {r J K q U V} {s : Site ops C r J K} {t : Site ops C q U V}
    (h : IndependentSites s t) (A : Hypernet ops r J K) (B : Hypernet ops q U V) :
    plugAtModuloIso (h.interchange A B).rightAfterLeft (Quotient.mk _ B) =
      plugAtModuloIso (h.interchange A B).leftAfterRight (Quotient.mk _ A) :=
  Quotient.sound ⟨(h.interchange A B).iso⟩

/-- The final context-validity condition is independent of the substitution order. -/
theorem IndependentSites.unique_iff {d I O} {C : Hypernet ops d I O}
    {r J K q U V} {s : Site ops C r J K} {t : Site ops C q U V}
    (h : IndependentSites s t) (A : Hypernet ops r J K) (B : Hypernet ops q U V) :
    UniqueHoles ops d (plugAt (h.interchange A B).rightAfterLeft B) ↔
      UniqueHoles ops d (plugAt (h.interchange A B).leftAfterRight A) :=
  DeepIso.uniqueHoles_iff (h.interchange A B).iso

end Hypernets.Linear

import Hypernets.Copying.FillingCollapse

/-! Every original addressed hole filling has a recursive specimen certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

def LabelCopy.reboundary {d I O J K} {G : Hypernet d I O} {label}
    (copy : LabelCopy G label) (hi : I = J) (ho : O = K) :
    LabelCopy (G.reboundary hi ho) label := by
  subst J
  subst K
  simpa only [Net.reboundary_refl] using copy

namespace BoxExpansion
variable {d I O} (C : Hypernet (d+1) I O) (e : C.Edge)
    (b : Box (alphabet d)) (label : C.edgeLabel e = .inr b)
    (L : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms))

def component : Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
    ((alphabet (d+1)).signature.output (C.edgeLabel e)) :=
  (box L).reboundary (by rw [label]; rfl) (by rw [label]; rfl)

def copy : LabelCopy (component C e b label L) (.inr ⟨b.bound,b.freeVariables,b.freeAtoms,L⟩) :=
  (LabelCopy.corolla _).reboundary _ _

noncomputable def family := SingleExpansion.family C e (component C e b label L)

/-- Expanding all retained edges and rebuilding one box restores the actual
body replacement, with identical outer incidences. -/
noncomputable def iso : DeepIso (C.expand (family C e b label L)) (replaceBox C e b label L) := by
  classical
  let labels := fun f => if f = e then Sum.inr (⟨b.bound,b.freeVariables,b.freeAtoms,L⟩ : Box (alphabet d)) else C.edgeLabel f
  have copies : ∀ f, LabelCopy (family C e b label L f) (labels f) := by
    intro f
    by_cases eq : f = e
    · subst f
      simpa only [family,SingleExpansion.selected,labels,ite_true] using copy C e b label L
    · simpa only [family,labels,ite_eq_right eq] using SingleExpansion.retained C e (component C e b label L) f eq
  exact DeepIso.ofIso (FillingCollapse.relabel C _ labels copies
    (by
      intro f
      by_cases eq : f = e
      · subst f; simp [labels,label,alphabet,nextAlphabet]
      · simp [labels,eq])
    (by
      intro f
      by_cases eq : f = e
      · subst f; simp [labels,label,alphabet,nextAlphabet]
      · simp [labels,eq]))

/-- Rebuilding the same original box from paired bodies gives paired outer edges. -/
theorem paired {T : PreTemplate}
    {R : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)}
    (inner : DeepFilling T b.body L R) (f : C.Edge) :
    DeepFillingEdge T C (family C e b label L) (family C e b label R) f := by
  classical
  by_cases eq : f = e
  · subst f
    exact .boxed b label inner (by simpa only [family,SingleExpansion.selected] using copy C e b label L)
      (by simpa only [family,SingleExpansion.selected] using copy C e b label R)
  · exact .retained (SingleExpansion.retained C e _ f eq) (SingleExpansion.retained C e _ f eq)
end BoxExpansion

namespace AddressedFillings

/-- Actual related replacements at an original sole hole are recursively paired,
up to explicit whole-result isomorphisms. No context is changed. -/
theorem paired (T : PreTemplate) {d I O} {C : Hypernet d I O} {r J K}
    (s : Site C r J K) (sole : SoleHole s) {G H : Hypernet r J K} (rel : T.Rel G H) :
    ∃ L R, DeepFilling T C L R ∧ Nonempty (DeepIso L (plugAt s G)) ∧
      Nonempty (DeepIso R (plugAt s H)) := by
  induction s with
  | shallow C e =>
    refine ⟨C.expand (SingleExpansion.family C e G),C.expand (SingleExpansion.family C e H),?_,
      ⟨SingleExpansion.iso C e G⟩,⟨SingleExpansion.iso C e H⟩⟩
    apply DeepFilling.expand
    intro f
    classical
    by_cases eq : f = e
    · subst f
      obtain ⟨h,hole⟩ := sole.1
      exact .filled h hole (by simpa only [SingleExpansion.selected] using rel)
    · exact .retained (SingleExpansion.retained C e G f eq) (SingleExpansion.retained C e H f eq)
  | @inside d I O C e b label r J K s ih =>
    obtain ⟨L,R,filling,⟨left⟩,⟨right⟩⟩ := ih sole.1 rel
    refine ⟨C.expand (BoxExpansion.family C e b label L),C.expand (BoxExpansion.family C e b label R),
      .expand _ _ _ (BoxExpansion.paired C e b label L filling),?_,?_⟩
    · exact ⟨(BoxExpansion.iso C e b label L).trans (replaceBox_deepIso C e b label left)⟩
    · exact ⟨(BoxExpansion.iso C e b label R).trans (replaceBox_deepIso C e b label right)⟩

/-- Every original binding-free closing observation supplies these certificates
and hole-free results. The statement quantifies over arbitrary host depth. -/
theorem closing (T : PreTemplate) {r k h} (C : ClosingContext r k h)
    (G H : OpenProgram r k h) (rel : T.Rel G.graph H.graph) :
    ∃ L R, DeepFilling T C.graph L R ∧ HoleFree L ∧ HoleFree R ∧
      Nonempty (DeepIso L (C.fill G.graph)) ∧ Nonempty (DeepIso R (C.fill H.graph)) := by
  obtain ⟨L,R,pair,⟨left⟩,⟨right⟩⟩ := paired T C.site C.sole rel
  exact ⟨L,R,pair,(allLabels_iso_iff _ left).mpr (C.fill_holeFree G.graph G.holeFree),
    (allLabels_iso_iff _ right).mpr (C.fill_holeFree H.graph H.holeFree),⟨left⟩,⟨right⟩⟩
end AddressedFillings
end Hypernets.Copying

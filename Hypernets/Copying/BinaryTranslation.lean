import Hypernets.Copying.TranslationClauses
import Hypernets.Graph.InterfaceShuffle

/-! Figure 16 application/binary clauses: retain the middle-block exchange
and D_{k,2}, D_{h,2}, with no simplification of the sharing graphs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph

/-- Pair the subterms, moving the left atoms past the right variables. -/
def pairBoundary (k h : Nat) :
    Net.Parallel.Boundary (Net.Tensor.interfaces [Wire.term] [Wire.term])
      (Net.Tensor.interfaces (environmentInterface k h) (environmentInterface k h))
      ([Wire.term] ++ [Wire.term])
      ((List.replicate k Wire.term ++ List.replicate k Wire.term) ++
        (List.replicate h Wire.atom ++ List.replicate h Wire.atom)) where
  inputs := Net.Tensor.ports _ _
  outputs := (Net.Tensor.ports (environmentInterface k h) (environmentInterface k h)).trans
    (InterfaceShuffle.bijection (List.replicate k Wire.term) (List.replicate h Wire.atom)
      (List.replicate k Wire.term) (List.replicate h Wire.atom))
  input_label := Net.Tensor.join_label _ _
  output_label b i := (InterfaceShuffle.label _ _ _ _ _).trans (Net.Tensor.join_label _ _ b i)

/-- Parallel translated subterms with exactly the grouped outputs in Figure 16. -/
def pair {d k h} (G H : Hypernet d [Wire.term] (environmentInterface k h)) :
    Hypernet d [.term,.term] (environmentInterface (k*2) (h*2)) :=
  castInterfaces rfl (by simp [environmentInterface, Nat.mul_two])
    (Net.Parallel.net (Net.Tensor.family G H) (pairBoundary k h)
      ⟨[false,true],by intro b; cases b <;> simp⟩)

/-- The application edge feeds the two subterms in left-to-right order. -/
def application {d k h} (G H : Hypernet d [Wire.term] (environmentInterface k h)) :
    Hypernet d [Wire.term] (environmentInterface k h) :=
  Serial.net (Serial.net (primitiveNet d (.operation .app)) (pair G H))
    (environmentDistributor d k h 2)

/-- Every binary example operation has the same prescribed argument wiring. -/
def binary {d k h} (o : Binary) (G H : Hypernet d [Wire.term] (environmentInterface k h)) :
    Hypernet d [Wire.term] (environmentInterface k h) :=
  Serial.net (Serial.net (primitiveNet d (.operation (.binary o))) (pair G H))
    (environmentDistributor d k h 2)

theorem pair_language {d k h} {G H : Hypernet d [Wire.term] (environmentInterface k h)}
    (g : LanguageGraph G) (h : LanguageGraph H) : LanguageGraph (pair G H) := by
  apply (allLabels_cast _ _ _ _).mpr
  intro ⟨b,e⟩
  cases b
  · exact g e
  · exact h e

theorem application_language {d k h} {G H : Hypernet d [Wire.term] (environmentInterface k h)}
    (g : LanguageGraph G) (h : LanguageGraph H) : LanguageGraph (application G H) :=
  Serial.allLabels_net _ (Serial.allLabels_net _ (allLabels_primitive _ _ _ trivial) (pair_language g h))
    (environmentDistributor_language _ _ _ _)

theorem binary_language {d k h} (o : Binary) {G H : Hypernet d [Wire.term] (environmentInterface k h)}
    (g : LanguageGraph G) (h : LanguageGraph H) : LanguageGraph (binary o G H) :=
  Serial.allLabels_net _ (Serial.allLabels_net _ (allLabels_primitive _ _ _ trivial) (pair_language g h))
    (environmentDistributor_language _ _ _ _)

end Hypernets.Copying.Translation

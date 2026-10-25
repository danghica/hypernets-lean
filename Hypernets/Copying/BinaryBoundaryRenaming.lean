import Hypernets.Copying.PairBoundaryRenaming

/-! Application and every original binary operation glue through their two-use forests. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TwoArgumentBoundary
open Graph

inductive Head where | application | binary (o : Binary)

def graph (d : Nat) : Head → Hypernet d [.term] [.term,.term]
  | .application => primitiveNet d (.operation .app)
  | .binary o => primitiveNet d (.operation (.binary o))

variable {d k h} {G H G' H' : Hypernet d [.term] (environmentInterface k h)}
    (head : Head) (f : BoundaryIso G G') (g : BoundaryIso H H')

theorem prefix_compatible : BoundarySerial.Compatible (BoundaryIso.refl (graph d head)) (PairBoundary.iso f g) := by
  intro i
  have law := PairBoundary.iso_input f g i
  rw [BoundaryIso.map_input] at law
  exact (Port.input.inj law).symm

def prefixIso := BoundarySerial.iso (BoundaryIso.refl (graph d head)) (PairBoundary.iso f g) (prefix_compatible head f g)

def forestIso (f : BoundaryIso G G') := MultiUseBoundary.ofTyped f.outputs (fun i => f.output_label i) d 2

/-- Agreement of the operands proves, rather than assumes, matching with the actual two-use forest. -/
theorem forest_compatible (agree : ∀ j, f.outputs.toFun j = g.outputs.toFun j) :
    BoundarySerial.Compatible (prefixIso head f g) (forestIso f) := by
  intro i
  obtain ⟨b,j,rfl⟩ := PairBoundary.index_surjective i
  have pref := BoundarySerial.iso_output (BoundaryIso.refl (graph d head)) (PairBoundary.iso f g) (prefix_compatible head f g) (PairBoundary.index b j)
  rw [BoundaryIso.map_output] at pref
  have paired := PairBoundary.iso_output f g agree b j
  rw [BoundaryIso.map_output] at paired
  have forest := MultiUseBoundary.ofTyped_pair_input f.outputs (fun i => f.output_label i) d b j
  rw [BoundaryIso.map_input] at forest
  exact (Port.output.inj pref).trans ((Port.output.inj paired).trans (Port.input.inj forest).symm)

def clause (head : Head) (G H : Hypernet d [.term] (environmentInterface k h)) :=
  Serial.net (Serial.net (graph d head) (Translation.pair G H)) (Translation.environmentDistributor d k h 2)

def iso (agree : ∀ j, f.outputs.toFun j = g.outputs.toFun j) :
    BoundaryIso (clause head G H) (clause head G' H') :=
  BoundarySerial.iso (prefixIso head f g) (forestIso f) (forest_compatible head f g agree)

theorem iso_output (agree : ∀ j, f.outputs.toFun j = g.outputs.toFun j) (i : Fin (environmentInterface k h).length) :
    (iso head f g agree).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have left := BoundarySerial.iso_output (prefixIso head f g) (forestIso f) (forest_compatible head f g agree) i
  have right := MultiUseBoundary.ofTyped_output f.outputs (fun i => f.output_label i) d 2 i
  rw [BoundaryIso.map_output] at right
  exact left.trans (congrArg Port.output (Port.output.inj right))
end Hypernets.Copying.TwoArgumentBoundary

namespace Hypernets.Copying.Translation
open Graph
variable {d k h} {G H G' H' : Hypernet d [.term] (environmentInterface k h)}
    (f : BoundaryIso G G') (g : BoundaryIso H H')
    (agree : ∀ j, f.outputs.toFun j = g.outputs.toFun j)

def application_boundaryIso : BoundaryIso (application G H) (application G' H') :=
  TwoArgumentBoundary.iso .application f g agree

def binary_boundaryIso (o : Binary) : BoundaryIso (binary o G H) (binary o G' H') :=
  TwoArgumentBoundary.iso (.binary o) f g agree

theorem application_boundaryIso_output (i : Fin (environmentInterface k h).length) :
    (application_boundaryIso f g agree).ports.toFun (.output i) = .output (f.outputs.toFun i) :=
  TwoArgumentBoundary.iso_output .application f g agree i

theorem binary_boundaryIso_output (o : Binary) (i : Fin (environmentInterface k h).length) :
    (binary_boundaryIso f g agree o).ports.toFun (.output i) = .output (f.outputs.toFun i) :=
  TwoArgumentBoundary.iso_output (.binary o) f g agree i
end Hypernets.Copying.Translation

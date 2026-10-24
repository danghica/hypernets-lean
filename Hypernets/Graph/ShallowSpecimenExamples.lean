import Hypernets.Graph.ShallowSpecimens
import Hypernets.Graph.ExpansionUnits
import Hypernets.Graph.OneWayExamples

/-! A genuine two-hole specimen and opposite one-way choices in paired fillings. -/
namespace Hypernets.Linear.Examples
open Graph

/-- The only hole occurrence in the earlier closed context is its selected edge. -/
theorem oneWayContext_hole_only {h : Hole} {e : oneWayContext.Edge}
    (label : holeAt operations 0 oneWayContext e = some h) : e = .inl (.inr 0) := by
  cases e with
  | inr e => cases label
  | inl e => cases e with
    | inl e => cases label
    | inr e =>
        have eq : e = 0 := Fin.ext (by have h : e.val < 1 := e.isLt; omega)
        subst e
        rfl

theorem oneWayContext_unique : UniqueHoles operations 0 oneWayContext := by
  intro h a b ha hb
  exact (oneWayContext_hole_only ha).trans (oneWayContext_hole_only hb).symm

theorem oneWayContext_no_retained (h : Hole) :
    ¬ RetainedHole oneWayContext (.inl (.inr 0)) h := by
  rintro ⟨e,ne,x,label⟩
  cases x with
  | inl u => exact ne (oneWayContext_hole_only label)
  | inr x => exact Empty.elim x

/-- Replace the earlier single hole by two consecutive distinct holes. -/
@[reducible] noncomputable def twoHoleFocusedContext :=
  oneWayContext.plug (.inl (.inr 0)) twoHoles

theorem twoHoleFocusedContext_unique : UniqueHoles operations 0 twoHoleFocusedContext :=
  plug_uniqueHoles_of_fresh oneWayContext (.inl (.inr 0)) twoHoles
    oneWayContext_unique twoHoles_unique (fun h retained _ => oneWayContext_no_retained h retained)

noncomputable def twoHoleFocus : Focussed twoHoleFocusedContext :=
  oneWayContext_focus.plug (.inl (.inr 0)) (by intro h; cases h) twoHoles twoHoles_focusFree

/-- Simultaneously fill both holes with variable corollas and retain the
focus and value by copies of their original corollas. -/
@[reducible] noncomputable def twoHoleFilling (e : twoHoleFocusedContext.Edge) :
    Hypernet operations 0 ((alphabet operations 0).signature.input (twoHoleFocusedContext.edgeLabel e))
      ((alphabet operations 0).signature.output (twoHoleFocusedContext.edgeLabel e)) :=
  match e with
  | .inl e => Net.corolla (alphabet operations 0).signature (oneWayContext.edgeLabel e.val)
  | .inr _ => variableFragment

/-- A concrete relation of equal, focus-free, one-way graphs. -/
def oneWayEquality : ConcretePreTemplate operations 0 where
  Rel G H := G = H ∧ FocusFree G ∧ OneWay G
  focus_free := by rintro I O G H ⟨rfl,free,_⟩; exact ⟨free,free⟩

theorem oneWayEquality_closed : oneWayEquality.OutputClosed :=
  fun related => Or.inl related.2.2

theorem twoHoleFilling_edges (e : twoHoleFocusedContext.Edge) :
    SpecimenEdge oneWayEquality twoHoleFocusedContext twoHoleFilling twoHoleFilling e := by
  cases e with
  | inl e =>
      have copy : ExpansionPaths.CorollaCopy twoHoleFocusedContext twoHoleFilling (.inl e) := {
        edge := (0 : Fin 1), label := rfl, source := rfl, target := rfl,
        only := fun x => Fin.ext (by have h : x.val < 1 := x.isLt; omega) }
      exact .retained copy copy
  | inr e =>
      exact SpecimenEdge.filled (C := twoHoleFocusedContext) (H := twoHoleFilling) (K := twoHoleFilling)
        (e := .inr e) (chainHole (if e = 0 then 0 else 1)) rfl
        ⟨rfl,variableFragment_focusFree,variable_oneWay⟩

theorem twoHoleFilling_closed : HoleFree (twoHoleFocusedContext.expand twoHoleFilling) := by
  apply ExpansionPaths.holeFree
  intro e
  cases e with
  | inr e => exact variableFragment_holeFree
  | inl e =>
      rintro h ⟨x,hx⟩
      have retained : RetainedHole oneWayContext (.inl (.inr 0)) h :=
        ⟨e.val,e.property,Sum.inl (),hx⟩
      exact oneWayContext_no_retained h retained

/-- A fully constructed concrete two-hole specimen, with actual closed states. -/
noncomputable def twoHoleSpecimen : ShallowSpecimen oneWayEquality (fun _ => True) where
  context := ⟨twoHoleFocusedContext,twoHoleFocusedContext_unique⟩
  focus := twoHoleFocus
  allowed := trivial
  left := twoHoleFilling
  right := twoHoleFilling
  edges := twoHoleFilling_edges
  left_closed := twoHoleFilling_closed
  right_closed := twoHoleFilling_closed

/-- The second hole alone is a non-operation path to the focus source. -/
theorem twoHoleSpecimen_not_rooted (kind : Op → OperationKind) :
    ¬ State.Rooted kind twoHoleSpecimen.leftState ∨ ¬ State.Rooted kind twoHoleSpecimen.rightState := by
  apply twoHoleSpecimen.not_both_rooted oneWayEquality_closed
    (Net.Path.single (G := twoHoleFocusedContext) (.inr 1)) rfl
  · change Net.Replacement.host oneWayContext (.inl (.inr 0)) twoHoles
      oneWayContext_focus.source ∈
      (twoHoles.target 1).map (Net.Replacement.insert oneWayContext (.inl (.inr 0)) twoHoles)
    exact List.mem_map.mpr ⟨.output (0 : Fin 1), by exact List.mem_singleton_self _, rfl⟩
  · exact List.mem_singleton_self _
  · exact id

/-- Boundary agreement now applies directly to the constructed specimen. -/
theorem twoHoleSpecimen_boundary :
    (twoHoleSpecimen.leftState.focussed.Initial ↔ twoHoleSpecimen.rightState.focussed.Initial) ∧
    (twoHoleSpecimen.leftState.focussed.Final ↔ twoHoleSpecimen.rightState.focussed.Final) :=
  twoHoleSpecimen.boundary_agreement

end Hypernets.Linear.Examples

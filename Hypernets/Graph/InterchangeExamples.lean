import Hypernets.Graph.SiteQuotient
import Hypernets.Graph.SequentialExamples
import Hypernets.Graph.CompositionExamples

/-! Deep interchange, equal box bodies, and nontrivial pointed quotient regressions. -/
namespace Hypernets.Linear.Examples
open Graph

def boxedSecondSite : Site operations boxedTwoHoles 0 [.term] [.term] :=
  .inside (G := boxedTwoHoles) 0 ⟨0,1,twoHoles⟩ rfl (.shallow twoHoles 1)

def boxedSitesIndependent : IndependentSites boxedFirstSite boxedSecondSite :=
  .same_box boxedTwoHoles 0 ⟨0,1,twoHoles⟩ rfl (.shallow twoHoles 0 1 (by decide))

/-- Different fillings commute inside a shared box even when one intermediate
graph has a repeated hole label. No intermediate freshness is assumed. -/
theorem boxed_interchange :
    plugAtModuloIso (boxedSitesIndependent.interchange repeatedHole variableFragment).rightAfterLeft
      (Quotient.mk _ variableFragment) =
    plugAtModuloIso (boxedSitesIndependent.interchange repeatedHole variableFragment).leftAfterRight
      (Quotient.mk _ repeatedHole) :=
  boxedSitesIndependent.interchange_modulo repeatedHole variableFragment

/-- Two distinct box edges deliberately carry exactly the same body. -/
@[reducible] def twinBoxes : Hypernet operations 1 [.thunk 0,.thunk 0] [] where
  Internal := Empty
  Edge := Fin 2
  finiteInternal := Enumeration.empty
  finiteEdge := Enumeration.fin 2
  internalLabel := Empty.elim
  edgeLabel _ := .inr ⟨0,0,singleHole⟩
  source e := [.input e]
  target _ := []
  source_nodup _ := by simp
  target_nodup _ := by simp
  source_unique := by
    intro v e f he hf
    simp only [List.mem_singleton] at he hf
    exact Port.input.inj (he.symm.trans hf)
  target_unique := by intro v e f he; cases he
  source_coverage v := by
    cases v with
    | internal x => exact Empty.elim x
    | input i => exact ⟨fun _ => by simp [Port.IsOutput], fun _ => ⟨i,by simp⟩⟩
    | output i => exact Fin.elim0 i
  target_coverage v := by
    cases v with
    | internal x => exact Empty.elim x
    | input i => simp [Port.IsInput]
    | output i => exact Fin.elim0 i
  source_typed e := by
    have cases : e = 0 ∨ e = 1 := by
      have h := e.isLt
      have h' : e.val = 0 ∨ e.val = 1 := by omega
      rcases h' with h | h
      · exact .inl (Fin.ext h)
      · exact .inr (Fin.ext h)
    rcases cases with rfl | rfl <;> rfl
  target_typed _ := rfl

def twinSite (e : Fin 2) : Site operations twinBoxes 0 [.term] [] :=
  .inside (G := twinBoxes) e ⟨0,0,singleHole⟩ rfl (.shallow singleHole 0)

def twinIndependent : IndependentSites (twinSite 0) (twinSite 1) :=
  .separate_boxes twinBoxes 0 1 (by decide) ⟨0,0,singleHole⟩ ⟨0,0,singleHole⟩
    rfl rfl (.shallow singleHole 0) (.shallow singleHole 0)

/-- Equal box labels do not conflate their occurrences: each receives its own filling. -/
theorem twin_interchange :
    plugAtModuloIso (twinIndependent.interchange value otherValue).rightAfterLeft (Quotient.mk _ otherValue) =
      plugAtModuloIso (twinIndependent.interchange value otherValue).leftAfterRight (Quotient.mk _ value) :=
  twinIndependent.interchange_modulo value otherValue

/-- A correctly transported deep occurrence represents the same pointed class. -/
theorem pointed_renamed_first :
    Quotient.mk (pointedSetoid operations 1 [.thunk 0] [.term] 0 [.term] [.term])
      ⟨boxedTwoHoles,boxedFirstSite⟩ =
    Quotient.mk (pointedSetoid operations 1 [.thunk 0] [.term] 0 [.term] [.term])
      ⟨renamedBoxedTwoHoles,renamedFirstSite⟩ :=
  Quotient.sound (.rename firstSites_correspond)

/-- The quotient does not collapse an incorrectly reused numerical address. -/
theorem pointed_wrong_address :
    Quotient.mk (pointedSetoid operations 1 [.thunk 0] [.term] 0 [.term] [.term])
      ⟨boxedTwoHoles,boxedFirstSite⟩ ≠
    Quotient.mk (pointedSetoid operations 1 [.thunk 0] [.term] 0 [.term] [.term])
      ⟨renamedBoxedTwoHoles,wrongRenamedSite⟩ := by
  intro eq
  exact wrong_address_changes_result ((Quotient.exact eq).plug repeatedHole)

end Hypernets.Linear.Examples

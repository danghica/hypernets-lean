import Hypernets.Graph.Focused
import Hypernets.Graph.CompositionExamples

/-! Nonvacuous boundary checks and rejection of hidden focuses. -/
namespace Hypernets.Linear.Examples
open Graph

/-- A focus followed by a unary hole, on the two-edge chain. -/
@[reducible] def focusChain (m : Focus) : Hypernet operations 0 [.term] [.term] :=
  twoHoles.relabelEdges (alphabet operations 0).signature
    (fun e => if e = 0 then focusLabel operations 0 m else ⟨.hole (chainHole 1)⟩)
    (by intro e; by_cases h : e = 0 <;> simp [alphabet, baseAlphabet, focusLabel, primitiveSignature, twoHoles, chainHole, h])
    (by intro e; by_cases h : e = 0 <;> simp [alphabet, baseAlphabet, focusLabel, primitiveSignature, twoHoles, chainHole, h])

def focusChain_focussed (m : Focus) : Focussed (focusChain m) where
  edge := 0
  mode := m
  label := rfl
  other_free := by
    intro e ne
    have eq : e = (1 : Fin 2) := by
      apply Fin.ext
      have := e.isLt
      have nz : e.val ≠ 0 := fun h => ne (Fin.ext h)
      omega
    subst e
    intro k bad
    cases bad
  source := .input 0
  target := .internal 0
  source_eq := by simp [focusChain, twoHoles]
  target_eq := by simp [focusChain, twoHoles]
  self_acyclic := by intro bad; cases bad
  not_exposed := by simp [Port.IsOutput]

theorem variableFragment_focusFree : FocusFree variableFragment := by
  intro e m bad
  cases bad

/-- A search focus remains initial after replacing the following hole. -/
theorem search_filling_initial :
    ((focusChain_focussed .search).plug 1 (by decide)
      variableFragment variableFragment_focusFree).Initial := by
  apply ((focusChain_focussed .search).plug_initial_iff 1 (by decide)
    variableFragment variableFragment_focusFree).mpr
  exact ⟨rfl, trivial⟩

/-- Backtracking at the input is final, whereas searching there is not. -/
theorem boundary_modes_distinct :
    (focusChain_focussed .backtrack).Final ∧ ¬ (focusChain_focussed .search).Final := by
  exact ⟨⟨rfl, trivial⟩, fun h => by cases h.1⟩

/-- A focus hidden inside a box violates global focus freedom, even though
the outer graph's sole edge is a box, not a focus. -/
theorem boxed_focus_not_free :
    ¬ FocusFree (box (bound := 0) (free := 1) (focusChain .search)) := by
  intro free
  have bad := free 0 (0 : Fin 2) .search
  apply bad
  rfl

end Hypernets.Linear.Examples

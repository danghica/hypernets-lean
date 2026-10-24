import Hypernets.Graph.ShallowSpecimenExamples

/-! Regression: output closure is pointwise, not a single global choice of side. -/
namespace Hypernets.Linear.AlternatingFillings
open Graph

@[reducible] def ops : Operations Unit := ⟨fun _ => 1, fun _ => []⟩
@[reducible] def variableWire : Hypernet ops 0 [.term] [.term] :=
  Net.corolla (alphabet ops 0).signature (primitiveLabel ops 0 .variable)
@[reducible] def operation : Hypernet ops 0 [.term] [.term] :=
  Net.corolla (alphabet ops 0).signature (primitiveLabel ops 0 (.operation ()))

/-- The original two-hole chain, using a signature that also has a unary operation. -/
@[reducible] def context : Hypernet ops 0 [.term] [.term] :=
  Examples.twoHoles.relabelEdges (alphabet ops 0).signature
    (fun e => primitiveLabel ops 0 (.hole (Examples.chainHole (if e = 0 then 0 else 1))))
    (by intro e; rfl) (by intro e; rfl)

@[reducible] def left (e : context.Edge) : Hypernet ops 0
    ((alphabet ops 0).signature.input (context.edgeLabel e))
    ((alphabet ops 0).signature.output (context.edgeLabel e)) :=
  if e = 0 then variableWire else operation

@[reducible] def right (e : context.Edge) : Hypernet ops 0
    ((alphabet ops 0).signature.input (context.edgeLabel e))
    ((alphabet ops 0).signature.output (context.edgeLabel e)) :=
  if e = 0 then operation else variableWire

theorem variable_oneWay : OneWay variableWire := by
  apply oneWay_iff.mpr
  intro j _ root
  have target : Port.output j ∈ variableWire.target 0 :=
    List.mem_map_of_mem (List.mem_finRange j)
  exact root.incoming_operation target

theorem operation_not_oneWay : ¬ OneWay operation := by
  intro one
  exact (oneWay_iff.mp one) 0 rfl ⟨0,[0],.cons (by trivial) (by decide) (by decide) (.nil _)⟩

/-- Each hole has a one-way side, but the side changes between the two holes. -/
theorem output_closed : ExpansionPaths.OutputClosedPair context left right := by
  intro e
  by_cases eq : e = 0
  · apply Or.inr; apply Or.inl
    change OneWay (if e = 0 then variableWire else operation)
    rw [ite_eq_left eq]
    exact variable_oneWay
  · apply Or.inr; apply Or.inr
    change OneWay (if e = 0 then operation else variableWire)
    rw [ite_eq_right eq]
    exact variable_oneWay

/-- Neither whole family consists solely of one-way fillings. -/
theorem no_global_oneWay_side : (¬ ∀ e, OneWay (left e)) ∧ (¬ ∀ e, OneWay (right e)) := by
  constructor
  · intro all; exact operation_not_oneWay (all (1 : Fin 2))
  · intro all; exact operation_not_oneWay (all (0 : Fin 2))

/-- The two-hole path is forbidden to lead to a jointly reachable term output,
even though neither side is globally one-way hole by hole. -/
theorem not_both_reachable :
    ¬ OperationReachable (context.expand left) (Net.Expansion.host context left (.output 0)) ∨
    ¬ OperationReachable (context.expand right) (Net.Expansion.host context right (.output 0)) := by
  classical
  by_cases l : OperationReachable (context.expand left) (Net.Expansion.host context left (.output 0))
  · right
    intro r
    have path : context.Path [0,1] := .cons ⟨.internal 0, by decide, by decide⟩ (Net.Path.single (G := context) 1)
    have result := ExpansionPaths.path_operations context left right output_closed path rfl
      (v := .output 0) (by decide) rfl l r 0 (by simp)
    exact result.1
  · exact Or.inl l

end Hypernets.Linear.AlternatingFillings

import Hypernets.Copying.AssignmentFrames

/-! Figure 19(c) with arbitrary matched atom trees and stable new values. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def beforePattern (d h : Nat) (O : List Wire) : Hypernet d (inputs h) (outputs O) :=
  (beforeFrame h O).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)
def afterPattern (d h : Nat) (O : List Wire) : Hypernet d (inputs h) (outputs O) :=
  (afterFrame h O).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def beforeFill {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (e : BeforeEdge) : Hypernet d
      ((alphabet d).signature.input ((beforePattern d h O).edgeLabel e))
      ((alphabet d).signature.output ((beforePattern d h O).edgeLabel e)) := by
  cases d <;> cases e
  all_goals first
    | exact G
    | exact primitiveNet _ (.operation (.binary .assign))
    | exact primitiveNet _ .instanceEdge
    | exact primitiveNet _ .store
    | exact T.net.relabel (alphabet _).signature (primitiveLabel _) (primitive_input _) (primitive_output _)

def afterFill {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (e : AfterEdge) : Hypernet d
      ((alphabet d).signature.input ((afterPattern d h O).edgeLabel e))
      ((alphabet d).signature.output ((afterPattern d h O).edgeLabel e)) := by
  cases d <;> cases e
  all_goals first
    | exact G
    | exact primitiveNet _ (.weakening .term)
    | exact primitiveNet _ .instanceEdge
    | exact primitiveNet _ .store
    | exact primitiveNet _ (.operation (.const .unit))
    | exact T.net.relabel (alphabet _).signature (primitiveLabel _) (primitive_input _) (primitive_output _)

def before {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Hypernet d (inputs h) (outputs O) := (beforePattern d h O).expand (beforeFill T G)
def after {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Hypernet d (inputs h) (outputs O) := (afterPattern d h O).expand (afterFill T G)

/-- A stable new value is mandatory; its graph and its outputs are retained. -/
inductive Rule : {d h : Nat} → {O : List Wire} → Hypernet d (inputs h) (outputs O) → Hypernet d (inputs h) (outputs O) → Prop where
  | assign {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G) :
      Rule (before T G) (after T G)

theorem rule_iff {d h O} {L R : Hypernet d (inputs h) (outputs O)} :
    Rule L R ↔ ∃ T G, Stable G ∧ L = before T G ∧ R = after T G := by
  constructor
  · intro s; cases s with | assign T G stable => exact ⟨T,G,stable,rfl,rfl⟩
  · rintro ⟨T,G,stable,rfl,rfl⟩; exact .assign T G stable

def beforeInstance {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (before T G).Edge := by
  cases d <;> exact ⟨.inst,(0 : Fin 1)⟩
def afterInstance {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (after T G).Edge := by
  cases d <;> exact ⟨.inst,(0 : Fin 1)⟩
def beforeStore {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (before T G).Edge := by
  cases d <;> exact ⟨.store,(0 : Fin 1)⟩
def afterStore {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (after T G).Edge := by
  cases d <;> exact ⟨.store,(0 : Fin 1)⟩
def beforeValue {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) : (before T G).Edge := by
  cases d <;> exact ⟨.value,e⟩
def afterValue {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) : (after T G).Edge := by
  cases d <;> exact ⟨.value,e⟩

theorem value_labels {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) :
    (before T G).edgeLabel (beforeValue T G e) = G.edgeLabel e ∧
    (after T G).edgeLabel (afterValue T G e) = G.edgeLabel e := by cases d <;> exact ⟨rfl,rfl⟩
theorem store_labels {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (before T G).edgeLabel (beforeStore T G) = primitiveLabel d .store ∧
    (after T G).edgeLabel (afterStore T G) = primitiveLabel d .store := by cases d <;> exact ⟨rfl,rfl⟩
end Hypernets.Copying.Assignment

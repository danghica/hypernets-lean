import Hypernets.Copying.Contexts
import Hypernets.Copying.TermContexts
import Hypernets.Contextual

/-! Concrete binding-free observation contexts, parameterised by execution.
The copying machine is a separate, still required implementation of this
interface. No determinism, robustness or translation law is postulated here. -/
namespace Hypernets.Copying
open Graph

structure OpenProgram (d k h : Nat) where
  graph : Hypernet d [.term] (environmentInterface k h)
  focusFree : FocusFree graph
  holeFree : HoleFree graph

structure ClosedProgram where
  depth : Nat
  graph : Hypernet depth [.term] []
  focusFree : FocusFree graph
  holeFree : HoleFree graph

noncomputable def ClosingContext.close {d k h} (C : ClosingContext d k h)
    (G : OpenProgram d k h) : ClosedProgram :=
  ⟨C.depth,C.fill G.graph,C.fill_focusFree _ G.focusFree,C.fill_holeFree _ G.holeFree⟩

/-- Execution is kept explicit until the full copying UAM is constructed.
The initializer accepts only closed, focus-free, hole-free program graphs. -/
structure Execution (State : Type u) where
  machine : Machine State
  initial : ClosedProgram → State

namespace Execution
variable {State : Type u} (E : Execution State)

/-- The depth is that of the fragment occurrence, not a bound on its context. -/
structure Interface where
  depth : Nat
  variables : Nat
  atoms : Nat

noncomputable def observations : Observations State Interface
    (fun i => OpenProgram i.depth i.variables i.atoms)
    (fun i => ClosingContext i.depth i.variables i.atoms) where
  allowed _ := True
  observe C G s := s = E.initial (C.close G)

/-- Exact successful termination; stuckness is not a positive observation. -/
def Terminates (P : ClosedProgram) : Prop :=
  ∃ n s, E.machine.Steps n (E.initial P) s ∧ E.machine.final s

/-- Definition 7.2 specialised to concrete single-term-hole binding-free
contexts. All context depths and all surrounding graph structures are quantified. -/
def Refines (Q : CostOrder) {d k h} (G H : OpenProgram d k h) : Prop :=
  ∀ C : ClosingContext d k h,
    E.machine.Refines Q (E.initial (C.close G)) (E.initial (C.close H))

def Equiv (Q : CostOrder) {d k h} (G H : OpenProgram d k h) : Prop :=
  E.Refines Q G H ∧ E.Refines Q H G

/-- The explicit graph-context formulation is exactly the generic observation
interface used by the robustness infrastructure. -/
theorem refines_iff_observations (Q : CostOrder) {d k h} (G H : OpenProgram d k h) :
    E.Refines Q G H ↔ E.observations.Refines E.machine Q
      (i := ⟨d,k,h⟩) G H := by
  constructor
  · intro ref C s t _ hs ht
    subst s; subst t
    exact ref C
  · intro ref C
    exact ref C trivial rfl rfl

theorem refines_refl (Q : CostOrder) {d k h} (G : OpenProgram d k h) :
    E.Refines Q G G := fun _ => Machine.Refines.refl Q _

theorem refines_trans {Q : CostOrder} {d k h} {G H K : OpenProgram d k h}
    (p : E.Refines Q G H) (q : E.Refines Q H K) : E.Refines Q G K :=
  fun C => (p C).trans (q C)

theorem equiv_refl (Q : CostOrder) {d k h} (G : OpenProgram d k h) : E.Equiv Q G G :=
  ⟨E.refines_refl Q G,E.refines_refl Q G⟩

theorem equiv_symm {Q : CostOrder} {d k h} {G H : OpenProgram d k h}
    (p : E.Equiv Q G H) : E.Equiv Q H G := ⟨p.2,p.1⟩

theorem equiv_trans {Q : CostOrder} {d k h} {G H K : OpenProgram d k h}
    (p : E.Equiv Q G H) (q : E.Equiv Q H K) : E.Equiv Q G K :=
  ⟨E.refines_trans p.1 q.1,E.refines_trans q.2 p.2⟩

/-- Forgetting costs gives precisely implication of successful termination.
This needs neither machine determinism nor a bound on running times. -/
theorem refines_any_iff {d k h} (G H : OpenProgram d k h) :
    E.Refines CostOrder.any G H ↔
      ∀ C : ClosingContext d k h, E.Terminates (C.close G) → E.Terminates (C.close H) := by
  constructor
  · intro ref C term
    obtain ⟨n,s,run,final⟩ := term
    obtain ⟨m,t,_,run',final'⟩ := ref C run final
    exact ⟨m,t,run',final'⟩
  · intro obs C n s run final
    obtain ⟨m,t,run',final'⟩ := obs C ⟨n,s,run,final⟩
    exact ⟨m,t,trivial,run',final'⟩

theorem equiv_any_iff {d k h} (G H : OpenProgram d k h) :
    E.Equiv CostOrder.any G H ↔
      ∀ C : ClosingContext d k h, E.Terminates (C.close G) ↔ E.Terminates (C.close H) := by
  constructor
  · intro eq C
    exact ⟨(E.refines_any_iff G H).mp eq.1 C,(E.refines_any_iff H G).mp eq.2 C⟩
  · intro eq
    exact ⟨(E.refines_any_iff G H).mpr (fun C => (eq C).mp),
      (E.refines_any_iff H G).mpr (fun C => (eq C).mpr)⟩
end Execution

/-- The unchanged term translation, padded to a common comparison allowance. -/
def translatedProgram {k h} (t : Term k h) (d : Nat) (bound : Translation.depth t ≤ d) :
    OpenProgram d k h where
  graph := Translation.padTo d bound (Translation.term t)
  focusFree := (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_focusFree t)
  holeFree := (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree t)

/-- Compare terms at every adequate fragment allowance, against all closing
binding-free contexts. The execution argument must eventually be the copying UAM. -/
def ObservationalEquiv {State : Type u} (E : Execution State) {k h} (t u : Term k h) : Prop :=
  ∀ d (ht : Translation.depth t ≤ d) (hu : Translation.depth u ≤ d),
    E.Equiv CostOrder.any (translatedProgram t d ht) (translatedProgram u d hu)

end Hypernets.Copying

import Hypernets.Copying.CombinedPadding

/-! Forward exact-cost padding for actual program executions and closed observations.
No converse simulation or padding-equivalence interface is assumed. -/
namespace Hypernets.Copying.Combined

/-- Add one unused layer to an unbounded state, keeping its actual token position. -/
def padUnbounded (s : UnboundedState) : UnboundedState := ⟨s.1+1,padState s.2⟩

theorem padUnbounded_final (s : UnboundedState) :
    unboundedMachine.final (padUnbounded s) ↔ unboundedMachine.final s := Iff.rfl

theorem unbounded_step_padding {s t : UnboundedState} (step : UnboundedStep s t) :
    UnboundedStep (padUnbounded s) (padUnbounded t) := by
  cases step with | lift step => exact .lift (step_padding step)

theorem unbounded_run_padding {s t : UnboundedState} {n} (run : unboundedMachine.Steps n s t) :
    unboundedMachine.Steps n (padUnbounded s) (padUnbounded t) := by
  induction run with
  | zero => exact .zero _
  | cons first rest ih => exact .cons (unbounded_step_padding first) ih

/-- Successful runs are preserved at exactly the same cost, for every cost preorder. -/
theorem padding_refines (Q : CostOrder) (s : UnboundedState) :
    unboundedMachine.Refines Q s (padUnbounded s) := by
  intro n t run done
  exact ⟨n,padUnbounded t,Q.refl n,unbounded_run_padding run,done⟩

theorem padding_initial (P : ClosedProgram) :
    padUnbounded (execution.initial P) = execution.initial (P.pad 1) :=
  congrArg (fun G => (⟨P.depth+1,G,(.search,.input 0)⟩ : UnboundedState)) (Padding.graph_eq_raise P.graph)

/-- Every finite increase of allowance preserves termination and all successful costs. -/
theorem initial_pad_refines (Q : CostOrder) (P : ClosedProgram) (n : Nat) :
    unboundedMachine.Refines Q (execution.initial P) (execution.initial (P.pad n)) := by
  induction n with
  | zero => exact Machine.Refines.refl _ _
  | succ n ih =>
    have one := padding_refines Q (execution.initial (P.pad n))
    rw [padding_initial] at one
    exact ih.trans one

/-- In particular, padding cannot destroy an existing successful execution. -/
theorem terminates_pad (P : ClosedProgram) (n : Nat) (done : execution.Terminates P) :
    execution.Terminates (P.pad n) := by
  obtain ⟨k,t,run,final⟩ := done
  obtain ⟨j,u,cost,run',final'⟩ := initial_pad_refines CostOrder.exact P n run final
  exact ⟨j,u,run',final'⟩

/-- Recursive renaming of closed initial graphs preserves costs for every preorder. -/
theorem initial_iso (Q : CostOrder) {d} {G H : Hypernet d [.term] []}
    (gf : FocusFree G) (gh : HoleFree G) (hf : FocusFree H) (hh : HoleFree H) (f : DeepIso G H) :
    unboundedMachine.Equiv Q (execution.initial ⟨d,G,gf,gh⟩) (execution.initial ⟨d,H,hf,hh⟩) :=
  represents_equiv Q (.lift {graph := f,mode := rfl,vertex := rfl})

/-- Padding the context and its fragment preserves every successful closed observation. -/
theorem close_pad_refines (Q : CostOrder) {d k h} (C : ClosingContext d k h)
    (G : OpenProgram d k h) (n : Nat) :
    unboundedMachine.Refines Q (execution.initial (C.close G))
      (execution.initial ((C.pad n).close (G.pad n))) := by
  have rename := initial_iso Q ((C.close G).pad n).focusFree ((C.close G).pad n).holeFree
    ((C.pad n).close (G.pad n)).focusFree ((C.pad n).close (G.pad n)).holeFree (C.pad_close_iso G n)
  exact (initial_pad_refines Q (C.close G) n).trans rename.1

end Hypernets.Copying.Combined

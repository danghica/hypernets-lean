import Hypernets.Copying.EqualPrefixCosts

/-! Quantitative consequences of the two shallow BPerm overlap diagrams.
These are claims about actual focused states, not yet whole-template robustness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined
namespace Opening
variable {d k h : Nat} {O : List Wire}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))
    (G : Hypernet (d+1) [.term] O)

/-- The two opened graphs agree as states, including their actual token positions. -/
def successorIso (action : Action f p) :
    StateIso ⟨Application.after B G,(.search,.input 0)⟩
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.after C G,(.search,.input 0)⟩) where
  graph := afterCompensated f p G action
  mode := rfl
  vertex := rfl

/-- Exact successful costs already agree before opening. Stability is the
original beta premise; no assumption about termination of the exposed body occurs. -/
theorem redex_costs (stable : Stable G) (action : Action f p) (cost : Nat) :
    TerminatesIn cost ⟨Application.before B G,(.search,.input 0)⟩ ↔
    TerminatesIn cost (InterfacePermutation.state (p.append (.refl O)).symm
      ⟨Application.before C G,(.search,.input 0)⟩) :=
  equal_prefix_costs (opening_diamond f p G stable action).1
    (opening_diamond f p G stable action).2.1 (successorIso f p G action) cost

/-- The complete beta overlap has equal exact costs in any outer typed context,
from the token positioned at this redex's input. The host may continue after
local return; the proof compares whole-host executions. -/
theorem redex_costs_at {I J} (K : Hypernet (d+1) I J) (e : K.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (K.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (K.edgeLabel e))
    (stable : Stable G) (action : Action f p) (cost : Nat) :
    TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      ⟨Application.before B G,(.search,.input 0)⟩)) ↔
    TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before C G,(.search,.input 0)⟩))) :=
  equal_prefix_costs_at K e hi ho (opening_diamond f p G stable action).1
    (opening_diamond f p G stable action).2.1 (successorIso f p G action) cost

/-- Forgetting exact costs yields termination equivalence for this actual
redex in each host, including the case where neither side terminates. -/
theorem redex_termination_at {I J} (K : Hypernet (d+1) I J) (e : K.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (K.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (K.edgeLabel e))
    (stable : Stable G) (action : Action f p) :
    (∃ cost, TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      ⟨Application.before B G,(.search,.input 0)⟩))) ↔
    (∃ cost, TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before C G,(.search,.input 0)⟩)))) :=
  exists_congr (redex_costs_at f p G K e hi ho stable action)
end Opening

namespace Copying
variable {d n k h : Nat} (T : ContractionTree .term (n+1))
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))

/-- Both paths hand off at the two-copy residual after exactly two transitions.
This cancels the prefix in every host but leaves, explicitly, the semantic
comparison of the residual boxes as the remaining obligation. -/
theorem residual_spectra_at {I J} (K : Hypernet (d+1) I J) (e : K.Edge)
    (hi : List.replicate (n+1) .term = (alphabet (d+1)).signature.input (K.edgeLabel e))
    (ho : environmentInterface k h = (alphabet (d+1)).signature.output (K.edgeLabel e))
    (action : Opening.Action f p) :
    (∀ cost, TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
        ⟨CopyRule.before T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩)) ↔
      TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
        (InterfacePermutation.state p.symm
          ⟨CopyRule.before T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩)))) ↔
    (∀ rest, TerminatesIn rest (plugState K e (Combined.castInterfaces hi ho
        ⟨CopyRule.after T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩)) ↔
      TerminatesIn rest (plugState K e (Combined.castInterfaces hi ho
        (InterfacePermutation.state p.symm
          ⟨CopyRule.after T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩)))) :=
  equal_prefix_spectra_at K e hi ho (initial_diamond T f p action).1
    (initial_diamond T f p action).2.1
end Copying
end Hypernets.Copying.BoxPermutation

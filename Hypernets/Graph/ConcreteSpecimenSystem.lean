import Hypernets.Graph.SpecimenRelocation
import Hypernets.Graph.ConcreteSafety

/-! A constructed concrete instance of the abstract specimen interface. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}

namespace ConcreteSafety
variable (T : LayeredPreTemplate ops) (Allowed : Hypernet ops d [.term] [] → Prop)
    (B : Behaviour ops d kind) (allowed : IsoClosedContexts Allowed)
    (closed : (T d).OutputClosed) (refocusing : RefocusingStates kind B.step)

/-- Every abstract locality field is supplied by a proved graph theorem. The
parameters concern the paper's context class, output closure, and behaviour. -/
noncomputable def system : SpecimenSystem (UAM.machine B) where
  Specimen := DeepSpecimen T Allowed
  left := DeepSpecimen.leftState
  right := DeepSpecimen.rightState
  mode S := S.focus.mode
  entering S := S.focus.Entering
  rooted := State.Rooted kind
  rooted_step := UAM.refocusing B refocusing
  same_final S := S.boundary_agreement.2
  context_step S := S.full_context_step B allowed closed

/-- The concrete quasi-specimen supplies the abstract rooted witness, without
assuming the endpoint comparisons before rootedness is available. -/
theorem quasi_bridge {A R} {s t : State ops d}
    (q : NonRewriteQuasi T Allowed kind A R s t) :
    (system T Allowed B allowed closed refocusing).Quasi A R s t := by
  intro hs ht
  exact NonRewriteQuasi.rooted_witness T Allowed kind q hs ht

/-- All three concrete input-safety alternatives imply the abstract rooted law. -/
theorem inputSafe_bridge {Q P : CostOrder}
    (safe : InputSafe T Allowed kind B Q P) :
    (system T Allowed B allowed closed refocusing).InputSafe Q P := by
  intro S _ _ mode enters
  rcases safe S mode enters with stuck | direct | quasi
  · exact .inl stuck
  · exact .inr (.inl direct)
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := quasi
    exact .inr (.inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩)

/-- The concrete robustness law supplies the abstract law: rootedness excludes
its unrooted alternative, and rewrite mode excludes a search transition. -/
theorem robust_bridge {Q P R : CostOrder}
    (robust : Robust T Allowed kind B Q P R) :
    (system T Allowed B allowed closed refocusing).Robust Q P R := by
  intro S hl hr mode remote t step
  have rewrite : UAM.Rewrite B S.leftState t := by
    rcases (UAM.step_iff B).mp step with search | rewrite
    · exact False.elim (State.search_not_rewrite search mode)
    · exact rewrite
  rcases Robust.rooted T Allowed kind B robust S hl hr mode remote rewrite with stuck | matching
  · exact .inl stuck
  · obtain ⟨k,l,s,t,cost,ls,rs,q⟩ := matching
    exact .inr ⟨k,l,s,t,cost,ls,rs,quasi_bridge T Allowed B allowed closed refocusing q⟩

/-- The lifting relation now uses actual concrete specimens and rooted endpoints. -/
theorem lifting_iff {s t : State ops d} :
    (system T Allowed B allowed closed refocusing).Lifting s t ↔
      ∃ S : DeepSpecimen T Allowed, Remote T Allowed S ∧
        State.Rooted kind S.leftState ∧ State.Rooted kind S.rightState ∧
        s = S.leftState ∧ t = S.rightState := Iff.rfl
end ConcreteSafety
end Hypernets.Linear

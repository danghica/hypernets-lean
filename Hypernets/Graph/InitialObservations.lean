import Hypernets.Graph.ClassConverse

/-! Initial observation witnesses built from unfocussed recursive fillings. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
namespace InitialObservations
variable {T : LayeredPreTemplate ops} {Allowed : Hypernet ops d [.term] [] → Prop}
    (C : Context ops d [.term] []) (free : FocusFree C.val)
    (H K : (e : C.val.Edge) → Hypernet ops d
      ((alphabet ops d).signature.input (C.val.edgeLabel e))
      ((alphabet ops d).signature.output (C.val.edgeLabel e)))
    (edges : ∀ e, DeepFillingEdge T C.val H K e)
    (hc : Allowed C.val) (allowed : IsoClosedContexts Allowed)
    (lh : HoleFree (C.val.expand H)) (rh : HoleFree (C.val.expand K))

/-- Insert a fresh initial focus in an arbitrary unfocussed paired filling. -/
noncomputable def specimen : DeepSpecimen T Allowed where
  context := ⟨FocusExpansion.inserted C.val (TypedPosition.initial C.val),
    (FocusInsertion.uniqueHoles_iff _ _ _ _ _).mpr C.property⟩
  focus := FocusInsertion.focussed C.val (TypedPosition.initial C.val).val.2 (TypedPosition.initial C.val).property (TypedPosition.initial C.val).not_output .search free
  allowed := allowed (FocusInsertion.underlying_iso C.val (TypedPosition.initial C.val).val.2 (TypedPosition.initial C.val).property (TypedPosition.initial C.val).not_output .search free).symm hc
  left := FocusExpansion.family C.val H (TypedPosition.initial C.val)
  right := FocusExpansion.family C.val K (TypedPosition.initial C.val)
  edges := FocusExpansion.edges_lift (TypedPosition.initial C.val) edges
  left_closed := FocusExpansion.closed (TypedPosition.initial C.val) H lh
  right_closed := FocusExpansion.closed (TypedPosition.initial C.val) K rh

/-- Observing a closed focus-free filling means starting at its unique input,
up to recursive state isomorphism. This definition does not mention a template. -/
def Observe (G : Hypernet ops d [.term] []) (s : DeepStateClass ops d) : Prop :=
  ∃ (f : FocusFree G) (h : HoleFree G),
    s = DeepStateClass.ofState ((TypedPosition.initial G).realize f h)

/-- The constructed left endpoint represents the independently initialized left filling. -/
theorem left_observation :
    Observe (C.val.expand H)
      (DeepStateClass.ofState (specimen C free H K edges hc allowed lh rh).leftState) := by
  have f := (DeepFilling.focusFree (.expand C.val H K edges) free).1
  refine ⟨f,lh,Quotient.sound ⟨Focussed.DeepIso.ofIso ?_⟩⟩
  exact Focussed.isoOfGraph (FocusExpansion.iso C.val H (TypedPosition.initial C.val))

/-- The same independent initialization identifies the right endpoint. -/
theorem right_observation :
    Observe (C.val.expand K)
      (DeepStateClass.ofState (specimen C free H K edges hc allowed lh rh).rightState) := by
  have f := (DeepFilling.focusFree (.expand C.val H K edges) free).2
  refine ⟨f,rh,Quotient.sound ⟨Focussed.DeepIso.ofIso ?_⟩⟩
  exact Focussed.isoOfGraph (FocusExpansion.iso C.val K (TypedPosition.initial C.val))

/-- A filled graph has a unique initial state class. -/
theorem observe_unique {G : Hypernet ops d [.term] []} {s t : DeepStateClass ops d}
    (hs : Observe G s) (ht : Observe G t) : s = t := by
  obtain ⟨f,h,rfl⟩ := hs
  obtain ⟨f',h',rfl⟩ := ht
  rfl

include free edges hc lh rh in
/-- General paired filling gives an actual allowed initial lifting witness. -/
theorem lifting {kind : Op → OperationKind} (B : Behaviour ops d kind)
    (closed : (T d).OutputClosed) (refocusing : RefocusingStates kind B.step)
    {s t : DeepStateClass ops d} (hs : Observe (C.val.expand H) s)
    (ht : Observe (C.val.expand K) t) :
    (ClassSpecimens.system T Allowed B allowed closed refocusing).Lifting s t := by
  let S := specimen C free H K edges hc allowed lh rh
  have initial : S.focus.Initial := ⟨rfl,trivial⟩
  have li := (ExpansionPaths.focussed_boundary _ _ S.focus S.focusCopies.1
    (fun e ne => (S.other_free e ne).1)).1.mpr initial
  have ri := S.boundary_agreement.1.mp li
  exact ⟨S,.inl (by intro h; cases h),DeepStateClass.initial_rooted li,
    DeepStateClass.initial_rooted ri,
    observe_unique hs (left_observation C free H K edges hc allowed lh rh),
    observe_unique ht (right_observation C free H K edges hc allowed lh rh)⟩
end InitialObservations
end Hypernets.Linear

import Hypernets.Graph.InsertionRenaming

/-! Exact coordinate characterization of erasure-based search from realized
states. No equality of raw vertex or edge names is assumed. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
    {G : Hypernet ops d [.term] []}

namespace TypedPosition

/-- Erasing a realized state returns an isomorphic underlying graph and the
original typed coordinate under that same isomorphism. -/
theorem coordinate_recovery (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G) :
    ∃ a : Net.Iso (p.realize fg hg).focussed.underlying G,
      (State.coordinate (p.realize fg hg)).rename a = p := by
  obtain ⟨a, h⟩ := FocusInsertion.underlying_position_exists G p.val.2 p.property p.not_output p.val.1 fg
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact h

/-- Search from a realized state is exactly coordinate search on its original
underlying graph, with a focus-preserving isomorphism allowed at the endpoint. -/
theorem search_realize_iff (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G)
    (kind : Op → OperationKind) (t : State ops d) :
    State.Search kind (p.realize fg hg) t ↔
      ∃ q : TypedPosition G, SearchStep G kind p.val q.val ∧
        Nonempty (Focussed.Iso (q.realize fg hg).focussed t.focussed) := by
  obtain ⟨a, ha⟩ := p.coordinate_recovery fg hg
  let s := p.realize fg hg
  let fs := s.focussed.underlying_focusFree
  let hs := s.focussed.underlying_holeFree s.hole_free
  constructor
  · rintro ⟨q, step, ⟨qt⟩⟩
    refine ⟨q.rename a, ?_, ⟨(q.realize_rename a fs hs fg hg).symm.trans qt⟩⟩
    have mapped := step.rename a
    change SearchStep G kind ((State.coordinate s).rename a).val (q.rename a).val at mapped
    rw [ha] at mapped
    exact mapped
  · rintro ⟨q, step, ⟨qt⟩⟩
    have source : p.rename a.symm = State.coordinate s := by
      exact (congrArg (rename a.symm) ha).symm.trans ((State.coordinate s).rename_symm a)
    have mapped := step.rename a.symm
    change SearchStep s.focussed.underlying kind (p.rename a.symm).val (q.rename a.symm).val at mapped
    rw [source] at mapped
    exact ⟨q.rename a.symm, mapped, ⟨(q.realize_rename a.symm fg hg fs hs).symm.trans qt⟩⟩

/-- Every coordinate search step now realizes a step of the explicit-state
relation between the two states inserted into the same underlying graph. -/
theorem search_realize (p q : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G)
    {kind : Op → OperationKind} (step : SearchStep G kind p.val q.val) :
    State.Search kind (p.realize fg hg) (q.realize fg hg) :=
  (p.search_realize_iff fg hg kind _).mpr ⟨q, step, ⟨Focussed.Iso.refl _⟩⟩

end TypedPosition
end Hypernets.Linear

import Hypernets.Graph.PatternRealization

/-! Search as context application of finite two-edge interaction fragments. -/
namespace Hypernets.Linear
open Graph PatternPlugging
variable {Op : Type} {ops : Operations Op} {d : Nat}

namespace State
/-- Finite interaction patterns plugged into a single shallow edge slot of a
focus-free, hole-free host. The selected edge is removed by both pluggings. -/
def ContextualSearch (kind : Op → OperationKind) (s t : State ops d) : Prop :=
  ∃ (C : Hypernet ops d [.term] []), FocusFree C ∧ HoleFree C ∧
    ∃ (e : C.Edge) (p q : Position C e),
      SearchStep (corolla C e) kind p.val q.val ∧ Matches C e p s ∧ Matches C e q t

/-- Every contextual finite-pattern step is an erasure-based state search step. -/
theorem contextualSearch_sound {kind : Op → OperationKind} {s t : State ops d}
    (step : ContextualSearch kind s t) : Search kind s t := by
  obtain ⟨C,free,closed,e,p,q,rule,sp,qt⟩ := step
  obtain ⟨a⟩ := (matches_iff C e p free closed s).mp sp
  obtain ⟨b⟩ := (matches_iff C e q free closed t).mp qt
  have run := (attached C e p).search_realize (attached C e q) free closed (PatternPlugging.sound C e rule)
  exact search_target_iso (search_source_iso run a) b

/-- Every erasure-based state search step factors through the same simple edge
slot and a pair of finite interaction fragments. -/
theorem contextualSearch_complete {kind : Op → OperationKind} {s t : State ops d}
    (step : Search kind s t) : ContextualSearch kind s t := by
  obtain ⟨q,run,⟨qt⟩⟩ := step
  let C := s.focussed.underlying
  obtain ⟨e,p',q',rule,hp,hq⟩ := PatternPlugging.complete C run
  have tp : (corolla C e).vertexLabel p'.2 = .term := by
    rw [← attach_label]
    exact (congrArg (fun z : SearchPosition C => C.vertexLabel z.2) hp).symm.trans (coordinate s).property
  have tq : (corolla C e).vertexLabel q'.2 = .term := rule.preserves_term tp
  let p : Position C e := ⟨p',tp⟩
  let r : Position C e := ⟨q',tq⟩
  have ep : attached C e p = coordinate s := Subtype.ext hp.symm
  have eq : attached C e r = q := Subtype.ext hq.symm
  refine ⟨C,s.focussed.underlying_focusFree,s.focussed.underlying_holeFree s.hole_free,e,p,r,rule,?_,?_⟩
  · apply (matches_iff C e p _ _ s).mpr
    rw [ep]
    exact ⟨recover s⟩
  · apply (matches_iff C e r _ _ t).mpr
    rw [eq]
    exact ⟨qt⟩

/-- Exact correspondence between erased state search and contextual finite-pattern rewriting. -/
theorem search_iff_contextual {kind : Op → OperationKind} {s t : State ops d} :
    Search kind s t ↔ ContextualSearch kind s t :=
  ⟨contextualSearch_complete,contextualSearch_sound⟩

/-- The independently defined incidence presentation has precisely the same contextual steps. -/
theorem incidenceSearch_iff_contextual {kind : Op → OperationKind} {s t : State ops d} :
    IncidenceSearch kind s t ↔ ContextualSearch kind s t :=
  search_iff_incidence.symm.trans search_iff_contextual

/-- Recursive search differs only by recursive renaming of a contextual successor. -/
theorem deepSearch_iff_contextual {kind : Op → OperationKind} {s t : State ops d} :
    DeepSearch kind s t ↔ ∃ u, ContextualSearch kind s u ∧ Nonempty (Focussed.DeepIso u.focussed t.focussed) := by
  rw [deepSearch_iff]
  simp only [search_iff_contextual]
end State
end Hypernets.Linear

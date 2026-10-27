import Hypernets.Copying.CopySearchReplay

/-! The copying UAM's intrinsic refocusing theorem, derived from the original rule. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

theorem copying_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.contraction .term)) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  have witness := rewrite_copy_certificate step ⟨e,head⟩
  cases witness with | certificate a => exact a.rooted root

/-- Exact search-prefix accounting for an actual copy in any context. -/
theorem copying_rooted_cost {d I O} {G H : Hypernet d I O} {v w e i n}
    (head : HeadAt G v e (.contraction .term)) (step : Rewrite G v H w)
    (run : (Search.machine G).Steps n (.search,.input i) (.rewrite,v)) :
    ∃ m, n = m+1 ∧ (Search.machine H).Steps m (.search,.input i) (.search,w) := by
  have witness := rewrite_copy_certificate step ⟨e,head⟩
  cases witness with | certificate a => exact a.rooted_cost run

/-- The intrinsic part of the actual full machine: unchanged search and contextual copying. -/
inductive IntrinsicStep {d I O} : State d I O → State d I O → Prop where
  | search (G : Hypernet d I O) {s t} (step : Search.Step G s t) : IntrinsicStep ⟨G,s⟩ ⟨G,t⟩
  | copy {G H : Hypernet d I O} {v w e} (head : HeadAt G v e (.contraction .term))
      (step : Rewrite G v H w) : IntrinsicStep ⟨G,(.rewrite,v)⟩ ⟨H,(.search,w)⟩

/-- The extrinsic part consists of actual contextual rewrites at operation heads. -/
inductive ComputeStep {d I O} : State d I O → State d I O → Prop where
  | operation {G H : Hypernet d I O} {v w e o} (head : HeadAt G v e (.operation o))
      (step : Rewrite G v H w) : ComputeStep ⟨G,(.rewrite,v)⟩ ⟨H,(.search,w)⟩

theorem IntrinsicStep.combined {d I O} {s t : State d I O} (step : IntrinsicStep s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | copy head step => exact .rewrite step

theorem ComputeStep.combined {d I O} {s t : State d I O} (step : ComputeStep s t) : Step s t := by
  cases step with | operation head step => exact .rewrite step

theorem intrinsic_compute_disjoint {d I O} {s t u : State d I O}
    (intrinsic : IntrinsicStep s t) (compute : ComputeStep s u) : False := by
  cases compute with
  | operation head step => cases intrinsic with
    | search G search => exact Search.no_rewrite search
    | copy other rewrite => cases (head_unique head other).2

/-- Exhaustive splitting of the existing machine, without changing any allowed transition. -/
theorem step_iff_intrinsic_or_compute {d I O} {s t : State d I O} :
    Step s t ↔ IntrinsicStep s t ∨ ComputeStep s t := by
  constructor
  · intro step
    cases step with
    | search G step => exact .inl (.search G step)
    | rewrite step =>
      obtain ⟨choice,e,head,_⟩ := rewrite_recognizes step
      rcases choice_head_active choice with copy | ⟨o,operation,_⟩
      · exact .inl (.copy (copy ▸ head) step)
      · exact .inr (.operation (operation ▸ head) step)
  · intro cases
    exact cases.elim IntrinsicStep.combined ComputeStep.combined

def Refocusing {d} (R : State d [.term] [] → State d [.term] [] → Prop) : Prop :=
  ∀ {s t}, Rooted s → R s t → Rooted t

theorem intrinsic_refocusing {d} : Refocusing (@IntrinsicStep d [.term] []) := by
  intro s t root step
  cases step with
  | search G step => exact Search.rooted_step root step
  | copy head step => exact copying_rooted head step root

/-- The intrinsic copying and search obligations are discharged; exactly operation refocusing remains. -/
theorem refocusing_iff_compute {d} : Refocusing (@Step d [.term] []) ↔ Refocusing (@ComputeStep d [.term] []) := by
  constructor
  · intro ref s t root step; exact ref root step.combined
  · intro ref s t root step
    rcases step_iff_intrinsic_or_compute.mp step with intrinsic | compute
    · exact intrinsic_refocusing root intrinsic
    · exact ref root compute

inductive UnboundedIntrinsicStep : UnboundedState → UnboundedState → Prop where
  | lift {d} {s t : State d [.term] []} (step : IntrinsicStep s t) : UnboundedIntrinsicStep ⟨d,s⟩ ⟨d,t⟩
inductive UnboundedComputeStep : UnboundedState → UnboundedState → Prop where
  | lift {d} {s t : State d [.term] []} (step : ComputeStep s t) : UnboundedComputeStep ⟨d,s⟩ ⟨d,t⟩

theorem unbounded_step_iff_intrinsic_or_compute {s t : UnboundedState} :
    UnboundedStep s t ↔ UnboundedIntrinsicStep s t ∨ UnboundedComputeStep s t := by
  constructor
  · intro step; cases step with
    | lift step =>
      rcases step_iff_intrinsic_or_compute.mp step with step | step
      · exact .inl (.lift step)
      · exact .inr (.lift step)
  · rintro (step | step)
    · cases step with | lift step => exact .lift step.combined
    · cases step with | lift step => exact .lift step.combined

def UnboundedRefocusing (R : UnboundedState → UnboundedState → Prop) : Prop :=
  ∀ {s t}, UnboundedRooted s → R s t → UnboundedRooted t

theorem unbounded_intrinsic_refocusing : UnboundedRefocusing UnboundedIntrinsicStep := by
  intro s t root step
  cases step with | lift step => exact intrinsic_refocusing root step

theorem unbounded_refocusing_iff_compute :
    UnboundedRefocusing UnboundedStep ↔ UnboundedRefocusing UnboundedComputeStep := by
  constructor
  · intro ref s t root step
    cases step with | lift step => exact ref root (.lift step.combined)
  · intro ref s t root step
    rcases unbounded_step_iff_intrinsic_or_compute.mp step with step | step
    · exact unbounded_intrinsic_refocusing root step
    · exact ref root step

/-- Every actual execution whose compute transitions preserve roots remains rooted. -/
theorem run_rooted {d n} {s t : State d [.term] []}
    (compute : Refocusing (@ComputeStep d [.term] []))
    (run : (machine d [.term] []).Steps n s t) (root : Rooted s) : Rooted t := by
  induction run with
  | zero => exact root
  | cons step run ih => exact ih (refocusing_iff_compute.mpr compute root step)
end Hypernets.Copying.Combined

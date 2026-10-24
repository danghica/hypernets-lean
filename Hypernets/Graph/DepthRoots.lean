import Hypernets.Graph.UnboundedDeterminism

/-! Exact rootedness under changing depth presentations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op} {kind : Op → OperationKind}

/-- Padding commutes with the canonical initial attachment. -/
theorem root {n} (s : DeepStateClass ops n) :
    stateClass (DeepStateClass.root s) = DeepStateClass.root (stateClass s) := by
  induction s using Quotient.inductionOn with
  | h s => exact Quotient.sound ⟨realizeIso s (TypedPosition.initial _)⟩

/-- Every successor of a padded class is itself the padding of an original successor. -/
theorem search_successor {n} {s : DeepStateClass ops n} {t : DeepStateClass ops (n+1)}
    (h : DeepStateClass.Search kind (stateClass s) t) :
    ∃ u, stateClass u = t ∧ DeepStateClass.Search kind s u := by
  induction s using Quotient.inductionOn with
  | h s =>
    induction t using Quotient.inductionOn with
    | h t =>
      obtain ⟨q,step,⟨iso⟩⟩ := h
      let r : TypedPosition s.focussed.underlying := ⟨q.val,q.property⟩
      let u := r.realize s.focussed.underlying_focusFree (s.focussed.underlying_holeFree s.hole_free)
      refine ⟨DeepStateClass.ofState u,Quotient.sound ⟨(realizeIso s r).trans iso⟩,r,?_,⟨Focussed.DeepIso.refl _⟩⟩
      rw [coordinate] at step
      exact searchStep_iff.mp ((underlying_search_iff s).mp step)

/-- An entire search execution starting at a padded state stays in its image. -/
theorem search_run_reflect {n k} {s : DeepStateClass ops n} {t : DeepStateClass ops (n+1)}
    (run : (DeepStateClass.searchMachine kind).Steps k (stateClass s) t) :
    ∃ u, stateClass u = t ∧ (DeepStateClass.searchMachine kind).Steps k s u := by
  generalize hs : stateClass s = start at run
  induction run generalizing s with
  | zero t => exact ⟨s,hs,.zero _⟩
  | cons step tail ih =>
    rw [← hs] at step
    obtain ⟨u,hu,step⟩ := search_successor step
    obtain ⟨v,hv,run⟩ := ih hu
    exact ⟨v,hv,.cons step run⟩

/-- Search rootedness is preserved and reflected, rather than just preserved. -/
theorem rooted_iff {n} (s : DeepStateClass ops n) :
    DeepStateClass.Rooted kind (stateClass s) ↔ DeepStateClass.Rooted kind s := by
  constructor
  · rintro ⟨k,run⟩
    rw [← root] at run
    obtain ⟨u,hu,run⟩ := search_run_reflect run
    have eq := stateClass_injective hu
    exact ⟨k,eq ▸ run⟩
  · rintro ⟨k,run⟩
    refine ⟨k,?_⟩
    rw [← root]
    exact (Unbounded.run_steps_iff _).mp
      (Unbounded.run_map stateClass (fun h => (class_search_iff kind _ _).mpr h)
        ((Unbounded.run_steps_iff _).mpr run))
end Hypernets.Linear.DepthPadding

import Hypernets.Graph.SearchHistoryStates

/-! Rootedness reflected back to a specified coordinate, not merely an isomorphic endpoint. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace TypedPosition
variable {G H K : Hypernet ops d [.term] []}

/-- Coordinate renaming follows composition of recursive graph isomorphisms. -/
theorem deepRename_trans (a : DeepIso G H) (b : DeepIso H K) (p : TypedPosition G) :
    (p.deepRename a).deepRename b = p.deepRename (DeepIso.trans a b) := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · change Port.map b.vertices.toFun (Port.map a.vertices.toFun p.val.2) =
      Port.map (DeepIso.trans a b).vertices.toFun p.val.2
    cases p.val.2 <;> rfl

/-- A focus-preserving isomorphism between inserted states induces an isomorphism
of their underlying graphs carrying the specified coordinates to each other. -/
theorem realization_coordinate_iso (p : TypedPosition G) (q : TypedPosition H)
    (fg : FocusFree G) (hg : HoleFree G) (fh : FocusFree H) (hh : HoleFree H)
    (f : Focussed.DeepIso (p.realize fg hg).focussed (q.realize fh hh).focussed) :
    ∃ a : DeepIso G H, p.deepRename a = q := by
  obtain ⟨a,pa⟩ := p.coordinate_recovery fg hg
  obtain ⟨b,qb⟩ := q.coordinate_recovery fh hh
  let a' := DeepIso.ofIso a
  let b' := DeepIso.ofIso b
  have pa' : (State.coordinate (p.realize fg hg)).deepRename a' = p := pa
  have qb' : (State.coordinate (q.realize fh hh)).deepRename b' = q := qb
  refine ⟨DeepIso.trans (DeepIso.symm a') (DeepIso.trans f.erased b'),?_⟩
  have inverse : p.deepRename (DeepIso.symm a') = State.coordinate (p.realize fg hg) :=
    (congrArg (deepRename (DeepIso.symm a')) pa').symm.trans
      (deepRename_symm a' (State.coordinate (p.realize fg hg)))
  rw [← deepRename_trans,← deepRename_trans,inverse,State.coordinate_deepIso f,qb']

/-- The canonical root of an inserted state is initial insertion on its original graph. -/
theorem root_class (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G) :
    DeepStateClass.root (DeepStateClass.ofState (p.realize fg hg)) =
      DeepStateClass.ofState ((initial G).realize fg hg) := by
  obtain ⟨a,_⟩ := p.coordinate_recovery fg hg
  have iso := (initial (p.realize fg hg).focussed.underlying).realize_rename a
    (p.realize fg hg).focussed.underlying_focusFree
    ((p.realize fg hg).focussed.underlying_holeFree (p.realize fg hg).hole_free) fg hg
  exact Quotient.sound ⟨Focussed.DeepIso.ofIso iso⟩

/-- All finite coordinate runs commute with recursive renaming. -/
theorem steps_deepRename (a : DeepIso G H) {n p q}
    (run : (coordinateMachine G kind).Steps n p q) :
    (coordinateMachine H kind).Steps n (p.map id (Port.map a.vertices.toFun))
      (q.map id (Port.map a.vertices.toFun)) := by
  induction run with
  | zero => exact .zero _
  | cons step _ ih => exact .cons (step.deepRename a) ih

/-- Rootedness of the actual inserted state is exactly initial search reachability
of its specified coordinate on the original graph. -/
theorem rooted_iff (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G) :
    State.Rooted kind (p.realize fg hg) ↔
      ∃ n, (coordinateMachine G kind).Steps n (.search,.input 0) p.val := by
  constructor
  · rintro ⟨n,run⟩
    rw [p.root_class fg hg] at run
    obtain ⟨q,trace,eq⟩ := (initial G).class_steps_lift fg hg run
    obtain ⟨iso⟩ := Quotient.exact eq
    obtain ⟨a,pa⟩ := q.realization_coordinate_iso p fg hg fg hg iso
    have mapped := steps_deepRename a trace
    change (coordinateMachine G kind).Steps n (.search,.input 0) (q.deepRename a).val at mapped
    rw [pa] at mapped
    exact ⟨n,mapped⟩
  · rintro ⟨n,run⟩
    exact p.realize_rooted fg hg run
end TypedPosition
end Hypernets.Linear

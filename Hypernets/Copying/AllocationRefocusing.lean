import Hypernets.Copying.HeadReplacementRefocusing

/-! Allocation is refocusing in every actual context, with the original stable rule premise. -/
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

theorem StateIso.rootedFrom {d I O} {s t : State d I O} (f : StateIso s t) (i : Fin I.length) :
    Search.RootedFrom s.1 i s.2 ↔ Search.RootedFrom t.1 i t.2 := by
  have eq : (s.2.1,Port.map f.graph.vertices.toFun s.2.2) = t.2 := Prod.ext f.mode f.vertex
  exact ((Search.rooted_iso f.graph i s.2).symm).trans (by rw [eq])

/-- The actual allocation result is rooted by head replacement and proved successor representation. -/
theorem allocation_rooted {d I O} {G H : Hypernet d I O} {v w e i}
    (head : HeadAt G v e (.operation (.unary .ref))) (step : Rewrite G v H w)
    (root : Search.RootedFrom G i (.rewrite,v)) : Search.RootedFrom H i (.search,w) := by
  obtain ⟨iso⟩ := rewrite_allocation_canonical step head
  exact (iso.rootedFrom i).mp (Search.replacement_rooted head (Allocation.filler G e head.1) root)

/-- The exact remaining extrinsic refocusing families, after discharging allocation. -/
inductive RemainingComputeStep {d I O} : State d I O → State d I O → Prop where
  | operation {G H : Hypernet d I O} {v w e o} (head : HeadAt G v e (.operation o))
      (other : o ≠ .unary .ref) (step : Rewrite G v H w) :
      RemainingComputeStep ⟨G,(.rewrite,v)⟩ ⟨H,(.search,w)⟩

theorem RemainingComputeStep.compute {d I O} {s t : State d I O} (step : RemainingComputeStep s t) :
    ComputeStep s t := by
  cases step with | operation head other step => exact .operation head step

theorem refocusing_iff_remaining_compute {d} :
    Refocusing (@Step d [.term] []) ↔ Refocusing (@RemainingComputeStep d [.term] []) := by
  rw [refocusing_iff_compute]
  constructor
  · intro ref s t root step; exact ref root step.compute
  · intro ref s t root step
    cases step with
    | @operation G H v w e o head step =>
      by_cases eq : o = .unary .ref
      · subst o; exact allocation_rooted head step root
      · exact ref root (.operation head eq step)

inductive UnboundedRemainingComputeStep : UnboundedState → UnboundedState → Prop where
  | lift {d} {s t : State d [.term] []} (step : RemainingComputeStep s t) :
      UnboundedRemainingComputeStep ⟨d,s⟩ ⟨d,t⟩

theorem unbounded_refocusing_iff_remaining_compute :
    UnboundedRefocusing UnboundedStep ↔ UnboundedRefocusing UnboundedRemainingComputeStep := by
  rw [unbounded_refocusing_iff_compute]
  constructor
  · intro ref s t root step
    cases step with | lift step => exact ref root (.lift step.compute)
  · intro ref s t root step
    cases step with
    | lift step => cases step with
      | @operation G H v w e o head step =>
        by_cases eq : o = .unary .ref
        · subst o; exact allocation_rooted head step root
        · exact ref root (.lift (.operation head eq step))

/-- Rootedness is invariant for an actual run once its remaining compute cases are proved. -/
theorem run_rooted_of_remaining {d n} {s t : State d [.term] []}
    (compute : Refocusing (@RemainingComputeStep d [.term] []))
    (run : (machine d [.term] []).Steps n s t) (root : Rooted s) : Rooted t := by
  induction run with
  | zero => exact root
  | cons step run ih => exact ih (refocusing_iff_remaining_compute.mpr compute root step)
end Hypernets.Copying.Combined

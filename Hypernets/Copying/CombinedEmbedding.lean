import Hypernets.Copying.CombinedExecution

/-! Every proved local execution embeds in the combined contextual subsystem,
with exactly its original cost. No independent execution oracle is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

theorem allocation_step {d O} {s t : Allocation.State d O} (step : Allocation.Step s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | allocate G stable => exact local_step (.allocate G stable)
  | allocate_suffix G stable K =>
    simpa only [serialLeft,left_input] using step_serialLeft K (local_step (.allocate G stable))

theorem allocation_run {d O} {s t : Allocation.State d O} {length}
    (run : (Allocation.machine d O).Steps length s t) :
    (machine d [.term] O).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (allocation_step step) ih

theorem dereference_step {d h} {s t : Dereference.State d h} (step : Dereference.Step s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | read T => exact local_step (.read T d)

theorem dereference_run {d h} {s t : Dereference.State d h} {length}
    (run : (Dereference.machine d h).Steps length s t) :
    (machine d (Dereference.inputs h) [.term]).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (dereference_step step) ih

theorem assignment_step {d h O} {s t : Assignment.State d h O} (step : Assignment.Step s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | assign T G stable => exact local_step (.assign T G stable)

theorem assignment_run {d h O} {s t : Assignment.State d h O} {length}
    (run : (Assignment.machine d h O).Steps length s t) :
    (machine d (Assignment.inputs h) (Assignment.outputs O)).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (assignment_step step) ih

theorem equality_step {d I O} {s t : AtomEquality.State d I O} (step : AtomEquality.Step s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | same T d => exact local_step (.same T d)
  | different T U d => exact local_step (.different T U d)

theorem equality_run {d I O} {s t : AtomEquality.State d I O} {length}
    (run : (AtomEquality.machine d I O).Steps length s t) :
    (machine d I O).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (equality_step step) ih

theorem application_step {d O} {s t : Application.State d O} (step : Application.Step s t) : Step s t := by
  cases step with
  | search G step => exact .search G step
  | beta B G stable => exact local_step (.beta B G stable)

theorem application_run {d O} {s t : Application.State d O} {length}
    (run : (Application.machine d O).Steps length s t) :
    (machine d [.term] O).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (application_step step) ih

theorem copying_step {d n k h} {s t : CopyRule.State d n k h} (step : CopyRule.Step s t) : Step s t := by
  cases step with
  | search step => exact .search _ step
  | copy T G copyable => exact local_step (.copy T G copyable)

theorem copying_run {d n k h} {s t : CopyRule.State d n k h} {length}
    (run : (CopyRule.machine d n k h).Steps length s t) :
    (machine d (List.replicate (n+1) .term) (environmentInterface k h)).Steps length s t := by
  induction run with
  | zero => exact .zero _
  | cons step run ih => exact .cons (copying_step step) ih

end Hypernets.Copying.Combined

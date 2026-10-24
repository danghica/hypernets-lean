import Hypernets.Graph.ExpansionCopies
import Hypernets.Graph.RecursiveIsoPlug

/-! Every finite simultaneous expansion is realizable by ordinary addressed substitutions. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}

/-- A finite run of actual shallow addressed substitutions, retaining the
outer interface and recording the number of substitutions. -/
inductive ShallowRun (ops : Operations Op) (d : Nat) (I O : List Wire) :
    Hypernet ops d I O → Nat → Hypernet ops d I O → Prop where
  | refl (C) : ShallowRun ops d I O C 0 C
  | cons (C : Hypernet ops d I O) (e : C.Edge)
      (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
        ((alphabet ops d).signature.output (C.edgeLabel e))) {n D}
      (tail : ShallowRun ops d I O (plugAt (.shallow C e) H) n D) :
      ShallowRun ops d I O C (n + 1) D

namespace ExpansionSequential
variable (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))

/-- A certified peeling execution. Each step uses the prescribed filling;
termination requires every remaining assignment to be an identity copy. -/
inductive Execution : (C : Hypernet ops d I O) →
    ((e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) → Nat → Hypernet ops d I O → Prop where
  | done (C : Hypernet ops d I O) (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e)) ((alphabet ops d).signature.output (C.edgeLabel e))) (copies : ∀ e, Nonempty (ExpansionPaths.CorollaCopy C H e)) : Execution C H 0 C
  | step (C : Hypernet ops d I O) (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e)) ((alphabet ops d).signature.output (C.edgeLabel e))) (e : C.Edge) {n D}
      (tail : Execution (C.plug e (H e)) (Net.ExpansionPeel.rest C H e) n D) : Execution C H (n+1) D

/-- Forget the filling schedule to obtain ordinary addressed substitution. -/
theorem Execution.ordinary {C H n D} (run : Execution (ops := ops) (d := d) (I := I) (O := O) C H n D) :
    ShallowRun ops d I O C n D := by
  induction run with
  | done C H copies => exact .refl C
  | step C H e tail ih => exact .cons C e (H e) ih

/-- Every completed peeling execution has the simultaneous result, up to
explicit isomorphism; this is proved from the steps, not included as a field. -/
theorem Execution.iso {C H n D} (run : Execution (ops := ops) (d := d) (I := I) (O := O) C H n D) :
    Nonempty (Net.Iso D (C.expand H)) := by
  classical
  induction run with
  | done C H copies => exact ⟨(ExpansionPaths.copiesIso C H (fun e => Classical.choice (copies e))).symm⟩
  | step C H e tail ih =>
      obtain ⟨iso⟩ := ih
      exact ⟨iso.trans (Net.ExpansionPeel.iso C H e)⟩

/-- Any two completed schedules have isomorphic results, even when their
orders and counts differ or some identity fillings are omitted. -/
theorem Execution.order_independent {C H n m D E}
    (left : Execution (ops := ops) (d := d) (I := I) (O := O) C H n D)
    (right : Execution C H m E) : Nonempty (Net.Iso D E) := by
  obtain ⟨l⟩ := left.iso
  obtain ⟨r⟩ := right.iso
  exact ⟨l.trans r.symm⟩

/-- Order independence also holds in the recursive graph quotient. -/
theorem Execution.order_independent_modulo {C H n m D E}
    (left : Execution (ops := ops) (d := d) (I := I) (O := O) C H n D)
    (right : Execution C H m E) :
    Quotient.mk (deepSetoid ops d I O) D = Quotient.mk (deepSetoid ops d I O) E := by
  obtain ⟨iso⟩ := left.order_independent right
  exact Quotient.sound ⟨DeepIso.ofIso iso⟩

/-- Remove every repeat of the selected edge and track surviving original
edges through the first ordinary substitution. Newly inserted edges are absent. -/
noncomputable def remaining (e : C.Edge) (es : List C.Edge) : List (C.plug e (H e)).Edge := by
  classical
  exact es.filterMap (fun f => if ne : f ≠ e then some (.inl ⟨f,ne⟩) else none)

theorem remaining_length (e : C.Edge) (es : List C.Edge) :
    (remaining C H e es).length ≤ es.length := List.length_filterMap_le _ _

theorem remaining_mem (e : C.Edge) (es : List C.Edge) (f : {f : C.Edge // f ≠ e})
    (mem : f.val ∈ es) : Sum.inl f ∈ remaining C H e es := by
  classical
  exact List.mem_filterMap.mpr ⟨f.val,mem,by simp [f.property]⟩

/-- Corollas outside the pending list remain corollas after peeling. -/
theorem remaining_copies (e : C.Edge) (es : List C.Edge)
    (copies : ∀ f, f ∉ e :: es → Nonempty (ExpansionPaths.CorollaCopy C H f)) :
    ∀ x, x ∉ remaining C H e es → Nonempty
      (ExpansionPaths.CorollaCopy (C.plug e (H e)) (Net.ExpansionPeel.rest C H e) x) := by
  intro x absent
  cases x with
  | inl f =>
      have notMem : f.val ∉ e :: es := by
        intro mem
        cases List.mem_cons.mp mem with
        | inl eq => exact f.property eq
        | inr mem => exact absent (remaining_mem C H e es f mem)
      obtain ⟨copy⟩ := copies f.val notMem
      exact ⟨{
        edge := copy.edge
        label := copy.label
        source := copy.source
        target := copy.target
        only := copy.only }⟩
  | inr x =>
      exact ⟨{
        edge := (0 : Fin 1)
        label := rfl
        source := rfl
        target := rfl
        only := fun i => Fin.ext (by have h : i.val < 1 := i.isLt; omega)}⟩

/-- Process any finite pending list covering all nontrivial fillings.
At most one substitution per list entry is required, and the final graph
is explicitly isomorphic to the simultaneous expansion. -/
theorem realize_list (es : List C.Edge)
    (copies : ∀ e, e ∉ es → Nonempty (ExpansionPaths.CorollaCopy C H e)) :
    ∃ n D, n ≤ es.length ∧ Execution C H n D := by
  classical
  suffices all : ∀ bound (C : Hypernet ops d I O)
      (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
        ((alphabet ops d).signature.output (C.edgeLabel e))) (es : List C.Edge),
      es.length = bound →
      (∀ e, e ∉ es → Nonempty (ExpansionPaths.CorollaCopy C H e)) →
      ∃ n D, n ≤ es.length ∧ Execution C H n D from
    all es.length C H es rfl copies
  intro bound
  induction bound using Nat.strongRecOn with
  | ind bound ih =>
    intro C H es size copies
    cases es with
    | nil =>
        exact ⟨0,C,by simp,.done C H (fun e => copies e (by simp))⟩
    | cons e es =>
        have shorter : (remaining C H e es).length < bound := by
          have h := remaining_length C H e es
          simp only [List.length_cons] at size
          omega
        obtain ⟨n,D,count,run⟩ := ih _ shorter (C.plug e (H e)) (Net.ExpansionPeel.rest C H e)
          (remaining C H e es) rfl (remaining_copies C H e es copies)
        refine ⟨n+1,D,?_,.step C H e run⟩
        have h := remaining_length C H e es
        simp only [List.length_cons]
        omega

/-- Any finite family, including cyclic/self-loop attachments and box-labelled
edges, is realizable by a finite sequence of shallow addressed substitutions. -/
theorem realize : ∃ n D, n ≤ C.finiteEdge.elements.length ∧ ShallowRun ops d I O C n D ∧
    Nonempty (Net.Iso D (C.expand H)) := by
  obtain ⟨n,D,bound,run⟩ := realize_list C H C.finiteEdge.elements
    (fun e absent => False.elim (absent (C.finiteEdge.complete e)))
  exact ⟨n,D,bound,run.ordinary,run.iso⟩

/-- The sequential and simultaneous results have the same recursive graph class. -/
theorem realize_modulo : ∃ n D, ShallowRun ops d I O C n D ∧
    Quotient.mk (deepSetoid ops d I O) D = Quotient.mk (deepSetoid ops d I O) (C.expand H) := by
  obtain ⟨n,D,_,run,⟨iso⟩⟩ := realize C H
  exact ⟨n,D,run,Quotient.sound ⟨DeepIso.ofIso iso⟩⟩

end ExpansionSequential
end Hypernets.Linear

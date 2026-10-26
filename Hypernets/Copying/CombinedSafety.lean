import Hypernets.Copying.CombinedSelection

/-! Recursive language safety through every local/contextual rewrite and complete run. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace RuleSafety

/-- Labels that can be introduced by the actual compute and copying rules. -/
structure Admits (P : Primitive → Prop) : Prop where
  operation : ∀ o, P (.operation o)
  instanceEdge : P .instanceEdge
  store : P .store
  weakening : ∀ s, P (.weakening s)
  contraction : ∀ s, P (.contraction s)

theorem serial_left (P : Primitive → Prop) {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (safe : AllLabels P (Serial.net G H)) : AllLabels P G := by
  intro e
  have h := safe (Serial.leftEdge G H e)
  rw [Serial.leftEdge_label] at h; exact h

theorem serial_right (P : Primitive → Prop) {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (safe : AllLabels P (Serial.net G H)) : AllLabels P H := by
  intro e
  have h := safe (Serial.rightEdge G H e)
  rw [Serial.rightEdge_label] at h; exact h

/-- Safety of a lambda-application source includes the body inside the selected box. -/
theorem application_body (P : Primitive → Prop) {d k h O}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)} {G : Hypernet (d+1) [.term] O}
    (safe : AllLabels P (Application.before B G)) : AllLabels P B := by
  have boxed := safe ⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩
  exact (Translation.allLabels_cast P rfl _ _).mp boxed

/-- The beta source also contains the whole argument, independently of its stability proof. -/
theorem application_argument (P : Primitive → Prop) {d k h O}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)} {G : Hypernet (d+1) [.term] O}
    (safe : AllLabels P (Application.before B G)) : AllLabels P G := by
  intro e
  exact safe ⟨true,⟨true,e⟩⟩

/-- Preservation includes the contents of every duplicated or opened nested box. -/
theorem local_allLabels (P : Primitive → Prop) (closed : Admits P)
    {d I O} {G H : Hypernet d I O} {v w} (step : Combined.Local G v H w)
    (safe : AllLabels P G) : AllLabels P H := by
  cases step with
  | allocate G stable =>
    exact Allocation.after_labels P G (serial_right P safe)
      closed.instanceEdge (closed.weakening _) (closed.contraction _) closed.store
  | read T d => exact Dereference.after_labels P T d closed.instanceEdge closed.store closed.weakening closed.contraction
  | assign T G stable =>
    have value : AllLabels P G := by
      intro e
      have h := safe (Assignment.beforeValue T G e)
      rw [(Assignment.value_labels T G e).1] at h; exact h
    exact Assignment.after_labels P T G value (closed.operation _) closed.instanceEdge closed.store closed.weakening (closed.contraction _)
  | same T d => exact AtomEquality.Same.after_labels P T d (closed.operation _) closed.instanceEdge closed.store closed.weakening (closed.contraction _)
  | different T U d => exact AtomEquality.Different.after_labels P T U d (closed.operation _) closed.instanceEdge closed.store closed.weakening (closed.contraction _)
  | beta B G stable => exact Application.after_labels P B G (application_body P safe) (application_argument P safe)
  | copy T G copyable => exact CopyRule.after_allLabels P T G (serial_right P safe) closed.weakening closed.contraction
  | unaryArithmetic d n => exact Translation.allLabels_primitive P d _ (closed.operation _)
  | binaryArithmetic o d m n => exact Translation.allLabels_primitive P d _ (closed.operation _)

/-- Context closure preserves the label property without requiring an erased host slot to satisfy it. -/
theorem rewrite_allLabels (P : Primitive → Prop) (closed : Admits P)
    {d I O} {G H : Hypernet d I O} {v w} (step : Combined.Rewrite G v H w)
    (safe : AllLabels P G) : AllLabels P H := by
  induction step with
  | «local» step => exact local_allLabels P closed step safe
  | rename f g step ih => exact (allLabels_iso_iff P g).mp (ih ((allLabels_iso_iff P f).mpr safe))
  | @plug I O C e G H v w step ih =>
    have result := ih (fun x => safe (.inr x))
    intro x
    cases x with
    | inl x => exact safe (.inl x)
    | inr x => exact result x
  | expand C F K e others step ih =>
    have result := ih (fun x => safe ⟨e,x⟩)
    rintro ⟨b,x⟩
    by_cases eq : b = e
    · subst b; exact result x
    · have old : AllLabels P (F b) := fun y => safe ⟨b,y⟩
      rw [others b eq] at old
      exact old x

/-- Runtime graphs additionally admit stores allocated by the machine. -/
def RuntimePrimitive (p : Primitive) : Prop := Translation.LanguagePrimitive p ∨ p = .store

def RuntimeGraph {d I O} (G : Hypernet d I O) : Prop := AllLabels RuntimePrimitive G

theorem admits_runtime : Admits RuntimePrimitive := by
  constructor
  · intro o; exact .inl True.intro
  · exact .inl True.intro
  · exact .inr rfl
  · intro s; exact .inl True.intro
  · intro s; exact .inl True.intro

/-- The initial translation alphabet is included in the runtime alphabet at every depth. -/
theorem language_runtime {d I O} {G : Hypernet d I O} (h : Translation.LanguageGraph G) : RuntimeGraph G := by
  induction d generalizing I O with
  | zero => intro e; exact Or.inl (h e)
  | succ d ih =>
    intro e
    have he := h e
    cases label : G.edgeLabel e with
    | inl p => exact Or.inl (by simpa [LabelAll,label] using he)
    | inr b => exact ih (by simpa [LabelAll,label,Translation.LanguageGraph,AllLabels] using he)

theorem admits_focusFree : Admits (fun p => ∀ m, p ≠ .focus m) := by
  constructor <;> intros <;> intro eq <;> cases eq

theorem admits_holeFree : Admits (fun p => ∀ h, p ≠ .hole h) := by
  constructor <;> intros <;> intro eq <;> cases eq
end RuleSafety

namespace Combined

theorem rewrite_runtime {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w)
    (safe : RuleSafety.RuntimeGraph G) : RuleSafety.RuntimeGraph H :=
  RuleSafety.rewrite_allLabels _ RuleSafety.admits_runtime step safe

theorem rewrite_focusFree {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w)
    (safe : FocusFree G) : FocusFree H := RuleSafety.rewrite_allLabels _ RuleSafety.admits_focusFree step safe

theorem rewrite_holeFree {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w)
    (safe : HoleFree G) : HoleFree H := RuleSafety.rewrite_allLabels _ RuleSafety.admits_holeFree step safe

theorem step_allLabels (P : Primitive → Prop) (closed : RuleSafety.Admits P)
    {d I O} {s t : State d I O} (step : Step s t) (safe : AllLabels P s.1) : AllLabels P t.1 := by
  cases step with
  | search => exact safe
  | rewrite step => exact RuleSafety.rewrite_allLabels P closed step safe

theorem run_allLabels (P : Primitive → Prop) (closed : RuleSafety.Admits P)
    {d I O} {s t : State d I O} {n} (run : (machine d I O).Steps n s t) (safe : AllLabels P s.1) : AllLabels P t.1 := by
  induction run with
  | zero => exact safe
  | cons step rest ih => exact ih (step_allLabels P closed step safe)

/-- No finite execution from a certified closed program acquires a hidden focus or hole. -/
theorem reachable_safe (P : ClosedProgram) {n t} (run : unboundedMachine.Steps n (execution.initial P) t) :
    FocusFree t.2.1 ∧ HoleFree t.2.1 := by
  obtain ⟨b,eq,bounded⟩ := run_bounded run (execution.initial P).2 rfl
  subst t
  exact ⟨run_allLabels _ RuleSafety.admits_focusFree bounded P.focusFree,
    run_allLabels _ RuleSafety.admits_holeFree bounded P.holeFree⟩

/-- Executions starting in the translation alphabet stay in the runtime alphabet, including stores. -/
theorem reachable_runtime (P : ClosedProgram) (language : Translation.LanguageGraph P.graph)
    {n t} (run : unboundedMachine.Steps n (execution.initial P) t) : RuleSafety.RuntimeGraph t.2.1 := by
  obtain ⟨b,eq,bounded⟩ := run_bounded run (execution.initial P).2 rfl
  subst t
  exact run_allLabels _ RuleSafety.admits_runtime bounded (RuleSafety.language_runtime language)
end Combined
end Hypernets.Copying

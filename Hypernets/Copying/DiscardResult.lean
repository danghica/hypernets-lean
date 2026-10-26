import Hypernets.Copying.AllocationCoherenceExamples

/-! A result and two explicit weakenings, used to describe actual store-operation successors.
This is a proof-side replacement graph; it adds no operational rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.DiscardResult
open Graph

theorem fin_one (i : Fin 1) : i = 0 := by omega
theorem fin_three (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega

/-- One returned constant, and explicit weakening of each of the two old arguments. -/
def label (c : Constant) (i : Fin 3) : Primitive :=
  if i.val = 0 then .operation (.const c) else .weakening .term

def source (i : Fin 3) : List (Port Empty 1 2) := if i.val = 0 then [.input 0] else []
def target (i : Fin 3) : List (Port Empty 1 2) :=
  if i.val = 0 then [] else if i.val = 1 then [.output 0] else [.output 1]

/-- The replacement keeps both outgoing wires, connected to distinct weakenings. -/
def base (c : Constant) : Net primitiveSignature [.term] [.term,.term] where
  Internal := Empty
  Edge := Fin 3
  finiteInternal := ⟨[],fun x => nomatch x⟩
  finiteEdge := Enumeration.fin 3
  internalLabel x := nomatch x
  edgeLabel := label c
  source := source
  target := target
  source_nodup i := by simp [source]; split <;> simp
  target_nodup i := by
    have eq : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases eq with rfl | rfl | rfl <;> simp [target]
  source_unique := by
    intro v e f he hf
    have cases3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases3 e with rfl | rfl | rfl <;>
      rcases cases3 f with rfl | rfl | rfl <;> simp_all [source]
  target_unique := by
    intro v e f he hf
    have cases3 (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases cases3 e with rfl | rfl | rfl <;>
      rcases cases3 f with rfl | rfl | rfl <;> simp_all [target]
  source_coverage := by
    intro v; cases v with
    | internal x => exact nomatch x
    | input i =>
      have eq : i = ⟨0,by decide⟩ := by apply Fin.ext; have := i.isLt; change i.val < 1 at this; change i.val = 0; omega
      subst i
      exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨0,by simp [source]⟩⟩
    | output i => simp [Port.IsOutput,source]
  target_coverage := by
    intro v; cases v with
    | internal x => exact nomatch x
    | input i =>
      simp only [Port.IsInput,not_true_eq_false,iff_false,not_exists]
      intro e
      have eq : e = 0 ∨ e = 1 ∨ e = 2 := by omega
      rcases eq with rfl | rfl | rfl <;> simp [target]
    | output i =>
      have eq : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        have := i.isLt; change i.val < 2 at this
        have h : i.val = 0 ∨ i.val = 1 := by omega
        exact h.elim (fun h => .inl (Fin.ext h)) (fun h => .inr (Fin.ext h))
      rcases eq with rfl | rfl
      · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨1,by simp [target]⟩⟩
      · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨2,by simp [target]⟩⟩
  source_typed i := by
    have eq : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases eq with rfl | rfl | rfl <;> rfl
  target_typed i := by
    have eq : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases eq with rfl | rfl | rfl <;> rfl

/-- Interpret the primitive replacement at any finite box allowance. -/
def net (d : Nat) (c : Constant) : Hypernet d [.term] [.term,.term] :=
  (base c).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)
end Hypernets.Copying.DiscardResult

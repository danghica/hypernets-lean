import Hypernets.Copying.ContextFilling

/-! Padding of observation contexts and reflection of observations from larger
allowances. Execution invariance is an explicit machine obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying

namespace Translation
@[simp] theorem padTo_add {d I O} (G : Hypernet d I O) (n : Nat) :
    padTo (d+n) (by omega) G = pad d n G := by
  have transport (m : Nat) (eq : m = n) :
      castDepth (congrArg (d+·) eq) (pad d m G) = pad d n G := by cases eq; rfl
  exact transport (d+n-d) (by omega)

/-- Choosing an intermediate sufficient allowance does not change the final graph. -/
theorem padTo_trans {d I O} (G : Hypernet d I O) (e N : Nat)
    (de : d ≤ e) (eN : e ≤ N) :
    padTo N eN (padTo e de G) = padTo N (Nat.le_trans de eN) G := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le de
  obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le eN
  rw [padTo_add, padTo_add]
  rw [pad_add]
  have cast_padTo {q r : Nat} (eq : q = r) (bound : d ≤ q) :
      castDepth eq (padTo q bound G) = padTo r (by omega) G := by
    cases eq; rfl
  have back := cast_padTo (Nat.add_assoc d n m).symm (by omega)
  rw [padTo_add] at back
  exact back
end Translation

namespace OpenProgram
/-- Add unused allowance without changing the represented open program. -/
def pad {d k h} (G : OpenProgram d k h) (n : Nat) : OpenProgram (d+n) k h where
  graph := Translation.pad d n G.graph
  focusFree := (Translation.allLabels_pad _ _ _ _).mpr G.focusFree
  holeFree := (Translation.allLabels_pad _ _ _ _).mpr G.holeFree
/-- The same padding to an explicitly chosen adequate allowance. -/
def padTo {d k h} (G : OpenProgram d k h) (N : Nat) (bound : d ≤ N) : OpenProgram N k h where
  graph := Translation.padTo N bound G.graph
  focusFree := (Translation.allLabels_padTo _ _ _ _).mpr G.focusFree
  holeFree := (Translation.allLabels_padTo _ _ _ _).mpr G.holeFree

/-- Admissibility proofs carry no extra program data. -/
theorem ext_graph {d k h} {G H : OpenProgram d k h} (eq : G.graph = H.graph) : G = H := by
  cases G; cases H; cases eq; rfl

@[simp] theorem padTo_add {d k h} (G : OpenProgram d k h) (n : Nat) :
    G.padTo (d+n) (by omega) = G.pad n := ext_graph (Translation.padTo_add _ _)

end OpenProgram

namespace ClosedProgram
/-- Pad a closed program, preserving the initializer's admissibility certificates. -/
def pad (G : ClosedProgram) (n : Nat) : ClosedProgram where
  depth := G.depth+n
  graph := Translation.pad G.depth n G.graph
  focusFree := (Translation.allLabels_pad _ _ _ _).mpr G.focusFree
  holeFree := (Translation.allLabels_pad _ _ _ _).mpr G.holeFree
end ClosedProgram

namespace ClosingContext
/-- Every original observation context lifts to a larger local allowance. -/
noncomputable def pad {d k h} (C : ClosingContext d k h) (n : Nat) : ClosingContext (d+n) k h where
  depth := C.depth+n
  graph := Translation.pad C.depth n C.graph
  site := Padding.padSite C.site n
  sole := Padding.padSite_sole C.site C.sole n
  bindingFree := (BindingFree.pad_iff _ _ _).mpr C.bindingFree

/-- Closing after padding is recursively isomorphic to padding after closing. -/
noncomputable def pad_close_iso {d k h} (C : ClosingContext d k h) (G : OpenProgram d k h) (n : Nat) :
    DeepIso ((C.close G).pad n).graph ((C.pad n).close (G.pad n)).graph :=
  Padding.pad_filling C.site G.graph n
end ClosingContext

namespace Execution
variable {State : Type u} (E : Execution State)

/-- A concrete execution must prove successful termination invariant under a
single unused layer of representation allowance. This is not an axiom. -/
def RespectsPadding : Prop :=
  ∀ P : ClosedProgram, E.machine.Equiv CostOrder.any (E.initial P) (E.initial (P.pad 1))

/-- The one-step machine obligation implies invariance under any finite padding. -/
theorem initial_pad (invariant : E.RespectsPadding) (P : ClosedProgram) (n : Nat) :
    E.machine.Equiv CostOrder.any (E.initial P) (E.initial (P.pad n)) := by
  induction n with
  | zero => exact ⟨Machine.Refines.refl _ _,Machine.Refines.refl _ _⟩
  | succ n ih =>
    have step := invariant (P.pad n)
    exact ⟨ih.1.trans step.1,step.2.trans ih.2⟩

/-- Padding a closing context and its fragment preserves the closed observation,
provided the execution discharges the two representation obligations. -/
theorem close_pad (iso : E.RespectsIso) (padding : E.RespectsPadding)
    {d k h} (C : ClosingContext d k h) (G : OpenProgram d k h) (n : Nat) :
    E.machine.Equiv CostOrder.any (E.initial (C.close G))
      (E.initial ((C.pad n).close (G.pad n))) := by
  have a := E.initial_pad padding (C.close G) n
  have b := iso ((C.close G).pad n).focusFree ((C.close G).pad n).holeFree
    ((C.pad n).close (G.pad n)).focusFree ((C.pad n).close (G.pad n)).holeFree
    (C.pad_close_iso G n)
  exact ⟨a.1.trans b.1,b.2.trans a.2⟩

/-- Refinement checked at a larger allowance reflects to the original allowance;
all original closing contexts are included by their proved padding lift. -/
theorem refines_of_pad (iso : E.RespectsIso) (padding : E.RespectsPadding)
    {d k h} {G H : OpenProgram d k h} (n : Nat)
    (rel : E.Refines CostOrder.any (G.pad n) (H.pad n)) : E.Refines CostOrder.any G H := by
  intro C
  exact (E.close_pad iso padding C G n).1.trans
    ((rel (C.pad n)).trans (E.close_pad iso padding C H n).2)

theorem equiv_of_pad (iso : E.RespectsIso) (padding : E.RespectsPadding)
    {d k h} {G H : OpenProgram d k h} (n : Nat)
    (rel : E.Equiv CostOrder.any (G.pad n) (H.pad n)) : E.Equiv CostOrder.any G H :=
  ⟨E.refines_of_pad iso padding n rel.1,E.refines_of_pad iso padding n rel.2⟩
/-- Reflection from any specified adequate allowance. -/
theorem equiv_of_padTo (iso : E.RespectsIso) (padding : E.RespectsPadding)
    {d k h} {G H : OpenProgram d k h} (N : Nat) (bound : d ≤ N)
    (rel : E.Equiv CostOrder.any (G.padTo N bound) (H.padTo N bound)) :
    E.Equiv CostOrder.any G H := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_add_of_le bound
  rw [OpenProgram.padTo_add,OpenProgram.padTo_add] at rel
  exact E.equiv_of_pad iso padding n rel

/-- Recursive isomorphism of open fragments is respected in every closing
context, by deep replacement congruence and the closed execution obligation. -/
theorem equiv_iso (iso : E.RespectsIso) {d k h} (G H : OpenProgram d k h)
    (f : DeepIso G.graph H.graph) : E.Equiv CostOrder.any G H := by
  have law (C : ClosingContext d k h) := iso (C.close G).focusFree (C.close G).holeFree
    (C.close H).focusFree (C.close H).holeFree (plugAt_deepIso C.site f)
  exact ⟨fun C => (law C).1,fun C => (law C).2⟩
end Execution
/-- Padding a translated program through an intermediate allowance is exact. -/
theorem translatedProgram_padTo {k h} (t : Term k h) (d N : Nat)
    (bound : Translation.depth t ≤ d) (larger : d ≤ N) :
    (translatedProgram t d bound).padTo N larger =
      translatedProgram t N (Nat.le_trans bound larger) :=
  OpenProgram.ext_graph (Translation.padTo_trans _ d N bound larger)

/-- It suffices to prove term equivalence at arbitrarily large common allowances,
provided the concrete execution proves both representation laws. -/
theorem observationalEquiv_iff_cofinal {State : Type u} (E : Execution State)
    (iso : E.RespectsIso) (padding : E.RespectsPadding) {k h} (t u : Term k h) :
    ObservationalEquiv E t u ↔
      ∀ b, ∃ N, b ≤ N ∧ ∃ ht : Translation.depth t ≤ N, ∃ hu : Translation.depth u ≤ N,
        E.Equiv CostOrder.any (translatedProgram t N ht) (translatedProgram u N hu) := by
  constructor
  · intro eq b
    let N := max b (max (Translation.depth t) (Translation.depth u))
    have hb : b ≤ N := Nat.le_max_left _ _
    have ht : Translation.depth t ≤ N := by omega
    have hu : Translation.depth u ≤ N := by omega
    exact ⟨N,hb,ht,hu,eq N ht hu⟩
  · intro high d ht hu
    obtain ⟨N,larger,ht',hu',eq⟩ := high d
    apply E.equiv_of_padTo iso padding N larger
    simpa only [translatedProgram_padTo] using eq
end Hypernets.Copying

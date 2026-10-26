import Hypernets.Copying.Allocation

/-! Representation laws for the concrete reference-allocation rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Allocation
open Graph

/-- Rename the preserved argument on the redex side. -/
def before_congr {d O} {G H : Hypernet d [.term] O} (f : DeepIso G H) :
    DeepIso (before G) (before H) := Serial.congr (DeepIso.refl _) f

/-- Rename the preserved argument on the allocated side. -/
def after_congr {d O} {G H : Hypernet d [.term] O} (f : DeepIso G H) :
    DeepIso (after G) (after H) := Serial.congr (DeepIso.refl _) f

/-- The stable side condition transports; no arbitrary argument becomes allocatable. -/
theorem renamed_rule {d O} {G H : Hypernet d [.term] O} (f : DeepIso G H) (stable : Stable G) :
    Rule (before H) (after H) := .allocate H (Stable.iso f stable)

/-- Canonical atom trees survive recursive padding with exactly their wiring. -/
theorem raise_tree (d : Nat) :
    raise d (CanonicalTree.atDepth .atom 1 d) = CanonicalTree.atDepth .atom 1 (d+1) := by
  cases d <;> rfl

noncomputable def prefix_raise (d : Nat) : DeepIso (raise d (cellPrefix d)) (cellPrefix (d+1)) := by
  unfold cellPrefix
  have f := (Padding.serial (Serial.net (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d))
    (primitiveNet d .store)).trans
    (Serial.congr (Padding.serial (primitiveNet d .instanceEdge) (CanonicalTree.atDepth .atom 1 d)) (DeepIso.refl _))
  simpa only [Padding.primitive,raise_tree] using f

noncomputable def before_raise {d O} (G : Hypernet d [.term] O) :
    DeepIso (raise d (before G)) (before (raise d G)) := by
  have f := Padding.serial (primitiveNet d (.operation (.unary .ref))) G
  simpa only [Padding.primitive,before] using f

noncomputable def after_raise {d O} (G : Hypernet d [.term] O) :
    DeepIso (raise d (after G)) (after (raise d G)) :=
  (Padding.serial (cellPrefix d) G).trans (Serial.congr (prefix_raise d) (DeepIso.refl _))

/-- The raw rule holds at a larger allowance with its stability premise proved. -/
theorem raised_rule {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
    Rule (before (raise d G)) (after (raise d G)) :=
  .allocate _ ((Stable.raise_iff G).mpr stable)

/-- Graph renaming is a representation change on either side of one allocation. -/
def UpToIso {d O} (L R : Hypernet d [.term] O) : Prop :=
  ∃ G : Hypernet d [.term] O, Stable G ∧ Nonempty (DeepIso L (before G)) ∧ Nonempty (DeepIso R (after G))

theorem rule_upToIso {d O} {L R : Hypernet d [.term] O} (h : Rule L R) : UpToIso L R := by
  obtain ⟨G,stable,rfl,rfl⟩ := rule_iff.mp h
  exact ⟨G,stable,⟨DeepIso.refl _⟩,⟨DeepIso.refl _⟩⟩

theorem upToIso_congr {d O} {L R L' R' : Hypernet d [.term] O}
    (a : DeepIso L L') (b : DeepIso R R') (h : UpToIso L R) : UpToIso L' R' := by
  obtain ⟨G,stable,⟨f⟩,⟨g⟩⟩ := h
  exact ⟨G,stable,⟨a.symm.trans f⟩,⟨b.symm.trans g⟩⟩

/-- This is an operational allocation-padding law, not an inference from determinism. -/
theorem upToIso_raise {d O} {L R : Hypernet d [.term] O} (h : UpToIso L R) :
    UpToIso (raise d L) (raise d R) := by
  obtain ⟨G,stable,⟨f⟩,⟨g⟩⟩ := h
  exact ⟨raise d G,(Stable.raise_iff G).mpr stable,
    ⟨(Padding.congr f).trans (before_raise G)⟩,⟨(Padding.congr g).trans (after_raise G)⟩⟩

/-- Finite iteration transports allocations to every higher depth allowance. -/
theorem upToIso_pad {d O} {L R : Hypernet d [.term] O} (h : UpToIso L R) (n : Nat) :
    UpToIso (Translation.pad d n L) (Translation.pad d n R) := by
  induction n with
  | zero => exact h
  | succ n ih => exact upToIso_raise ih
end Hypernets.Copying.Allocation

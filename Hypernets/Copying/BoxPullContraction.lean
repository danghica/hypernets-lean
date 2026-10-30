import Hypernets.Copying.BoxPullContractionFrame
import Hypernets.Copying.TemplateInputSafety
import Hypernets.Copying.TranslationClauses

/-! The literal BPullC pair of Figure 21 for both sharing sorts. The two
adjacent free outputs of an arbitrary focus-free body are contracted inside
the box on the left and outside it on the right. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph

def variables (s : ShareSort) (k m : Nat) : Nat :=
  match s with | .term => k+m | .atom => k

def atoms (s : ShareSort) (h m : Nat) : Nat :=
  match s with | .term => h | .atom => m+h

/-- In both sorts the selected wires occur between the old term and atom
blocks. Atom positions are therefore before the original atom outputs. -/
theorem block_interface (s : ShareSort) (k h m : Nat) :
    environmentInterface (variables s k m) (atoms s h m) =
      List.replicate k .term ++ (List.replicate m s.wire ++ List.replicate h .atom) := by
  cases s <;> simp [variables,atoms,environmentInterface,ShareSort.wire,
    ← List.replicate_append_replicate,List.append_assoc]

theorem variables_bound (s : ShareSort) (n k m : Nat) :
    variables s (n+k) m = n + variables s k m := by
  cases s <;> simp [variables,Nat.add_assoc]

/-- Contract the two displayed resources of one environment, preserving
the entire original graph and the remaining interface order. -/
def contract {d I k h} (s : ShareSort)
    (G : Hypernet d I (environmentInterface (variables s k 2) (atoms s h 2))) :
    Hypernet d I (environmentInterface (variables s k 1) (atoms s h 1)) :=
  Translation.castInterfaces rfl (by simpa using (block_interface s k h 1).symm)
    (merge s (Translation.castInterfaces rfl (by simpa using block_interface s k h 2) G))

/-- The body contraction acts only on free outputs: the first n bound
outputs remain fixed, including when there are no other free variables. -/
def body {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    Hypernet d [.term] (environmentInterface (n+variables s k 1) (atoms s h 1)) :=
  Translation.castInterfaces rfl (by rw [variables_bound])
    (contract s (Translation.castInterfaces rfl (by rw [variables_bound]) G))

def left {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    Hypernet (d+1) [.thunk n] (environmentInterface (variables s k 1) (atoms s h 1)) :=
  box (bound := n) (freeVariables := variables s k 1) (body s G)

def right {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    Hypernet (d+1) [.thunk n] (environmentInterface (variables s k 1) (atoms s h 1)) :=
  contract s (box (bound := n) (freeVariables := variables s k 2) G)

/-- Every body is permitted, with the paper's focus-freedom condition; no
closedness, copyability, or operation restriction is imposed on it. -/
inductive Step : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | pull {d n k h} (s : ShareSort)
      (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2)))
      (free : FocusFree G) : Step (left s G) (right s G)

inductive UpToIso : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step A B) (right : DeepIso B H) : UpToIso G H

/-- Output merging adds exactly its contraction and preserves every
primitive in the original graph, recursively through all box bodies. -/
theorem merge_allLabels (P : Primitive → Prop) {d I A B} (s : ShareSort)
    (G : Hypernet d I (A ++ s.wire :: s.wire :: B)) :
    AllLabels P (merge s G) ↔ AllLabels P G ∧ P (.contraction s) := by
  constructor
  · intro all
    cases d <;> exact ⟨fun e => all ⟨false,e⟩,all ⟨true,(0 : Fin 1)⟩⟩
  · rintro ⟨all,contraction⟩
    cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first | exact all e | exact contraction

theorem contract_allLabels (P : Primitive → Prop) {d I k h} (s : ShareSort)
    (G : Hypernet d I (environmentInterface (variables s k 2) (atoms s h 2))) :
    AllLabels P (contract s G) ↔ AllLabels P G ∧ P (.contraction s) := by
  unfold contract
  rw [Translation.allLabels_cast,merge_allLabels,Translation.allLabels_cast]

theorem body_allLabels (P : Primitive → Prop) {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    AllLabels P (body s G) ↔ AllLabels P G ∧ P (.contraction s) := by
  unfold body
  rw [Translation.allLabels_cast,contract_allLabels,Translation.allLabels_cast]

theorem left_allLabels (P : Primitive → Prop) {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    AllLabels P (left s G) ↔ AllLabels P G ∧ P (.contraction s) := by
  constructor
  · intro all; exact (body_allLabels P s G).mp (all (0 : Fin 1))
  · intro all e; exact (body_allLabels P s G).mpr all

theorem right_allLabels (P : Primitive → Prop) {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2))) :
    AllLabels P (right s G) ↔ AllLabels P G ∧ P (.contraction s) := by
  rw [right,contract_allLabels]
  constructor
  · rintro ⟨all,contraction⟩; exact ⟨all (0 : Fin 1),contraction⟩
  · rintro ⟨all,contraction⟩; exact ⟨fun _ => all,contraction⟩

theorem Step.focusFree {d I O} {G H : Hypernet d I O} (step : Step G H) :
    FocusFree G ∧ FocusFree H := by
  cases step with
  | pull s B free => exact ⟨(left_allLabels _ s B).mpr ⟨free,by intro m eq; cases eq⟩,
      (right_allLabels _ s B).mpr ⟨free,by intro m eq; cases eq⟩⟩

theorem Step.allLabels (P : Primitive → Prop) {d I O} {G H : Hypernet d I O}
    (step : Step G H) : AllLabels P G ↔ AllLabels P H := by
  cases step with
  | pull s B _ => exact (left_allLabels P s B).trans (right_allLabels P s B).symm

theorem UpToIso.focusFree {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f p g => exact ⟨(allLabels_iso_iff _ f).mpr p.focusFree.1,
      (allLabels_iso_iff _ g).mp p.focusFree.2⟩

theorem UpToIso.allLabels (P : Primitive → Prop) {d I O} {G H : Hypernet d I O}
    (pair : UpToIso G H) : AllLabels P G ↔ AllLabels P H := by
  cases pair with
  | witness f p g => exact (allLabels_iso_iff _ f).trans ((p.allLabels P).trans (allLabels_iso_iff _ g))

def template : PreTemplate where
  Rel := UpToIso
  focus_free pair := pair.focusFree

theorem literal {d n k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (n+variables s k 2) (atoms s h 2)))
    (free : FocusFree G) : template.Rel (left s G) (right s G) :=
  .witness (DeepIso.refl _) (.pull s G free) (DeepIso.refl _)

end Hypernets.Copying.BoxPullContraction

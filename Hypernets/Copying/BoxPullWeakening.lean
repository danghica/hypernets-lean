import Hypernets.Copying.TemplateInputSafety
import Hypernets.Copying.TranslationClauses
import Hypernets.Graph.InterfaceShuffle

/-! The literal BPullW pair of Figure 21.  The extra weakening is inserted
between the free term and atom blocks, both inside and outside the box.
The bound outputs stay first and are never permuted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph

/-- Adding one resource of the chosen sort changes only that environment. -/
def variables (s : ShareSort) (k : Nat) : Nat :=
  match s with | .term => k + 1 | .atom => k

def atoms (s : ShareSort) (h : Nat) : Nat :=
  match s with | .term => h | .atom => h + 1

/-- The ordered boundary places the new resource between the two existing
blocks. The original component's incidences retain their order. -/
def insertionBoundary (I A B : List Wire) (s : ShareSort) :
    Net.Parallel.Boundary (Net.Tensor.interfaces I [])
      (Net.Tensor.interfaces (A ++ B) [s.wire])
      (I ++ []) ((A ++ [s.wire]) ++ (B ++ [])) where
  inputs := Net.Tensor.ports I []
  outputs := (Net.Tensor.ports (A ++ B) [s.wire]).trans
    (InterfaceShuffle.bijection A B [s.wire] [])
  input_label := Net.Tensor.join_label I []
  output_label b i :=
    (InterfaceShuffle.label A B [s.wire] [] _).trans
      (Net.Tensor.join_label (A ++ B) [s.wire] b i)

/-- Disjoint juxtaposition with one actual weakening edge, using that ordered
boundary. This construction introduces no machine transition. -/
def insert {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    Hypernet d (I ++ []) ((A ++ [s.wire]) ++ (B ++ [])) :=
  Net.Parallel.net (Net.Tensor.family G (primitiveNet d (.weakening s)))
    (insertionBoundary I A B s) ⟨[false,true], by intro b; cases b <;> simp⟩

/-- The resulting boundary has exactly one additional variable or atom. -/
theorem extended_interface (s : ShareSort) (k h : Nat) :
    ((List.replicate k Wire.term ++ [s.wire]) ++
      (List.replicate h Wire.atom ++ [])) =
      environmentInterface (variables s k) (atoms s h) := by
  cases s <;> simp only [variables,atoms,ShareSort.wire,environmentInterface,List.append_nil]
  · change (List.replicate k Wire.term ++ List.replicate 1 Wire.term) ++ _ = _
    rw [List.replicate_append_replicate]
  · rw [List.append_assoc]
    simp [List.replicate_succ, List.cons_append]

/-- Extend the free environment without changing any existing boundary
position within its term or atom block. -/
def extend {d I k h} (G : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    Hypernet d I (environmentInterface (variables s k) (atoms s h)) :=
  (insert G s).reboundary (List.append_nil I) (extended_interface s k h)

/-- Extending a body leaves its first n bound term outputs unchanged. -/
theorem variables_bound (s : ShareSort) (n k : Nat) :
    variables s (n + k) = n + variables s k := by
  cases s <;> simp [variables,Nat.add_assoc]

def body {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Hypernet d [.term] (environmentInterface (n + variables s k) (atoms s h)) :=
  (extend G s).reboundary rfl (by rw [variables_bound])

/-- The weakening is inside the box, alongside the unchanged original body. -/
def left {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Hypernet (d+1) [.thunk n] (environmentInterface (variables s k) (atoms s h)) :=
  box (bound := n) (freeVariables := variables s k) (body G s)

/-- The same weakening is outside the box, which contains the original body. -/
def right {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) :
    Hypernet (d+1) [.thunk n] (environmentInterface (variables s k) (atoms s h)) :=
  extend (box (bound := n) (freeVariables := k) G) s

/-- Both literal sharing-sort instances of BPullW, with the paper's
focus-free body condition. -/
inductive Step : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | pull {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
      (s : ShareSort) (free : FocusFree G) : Step (left G s) (right G s)

/-- Ordered recursive graph representation may vary on either side. -/
inductive UpToIso : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step A B) (right : DeepIso B H) : UpToIso G H

/-- Insertion retains the complete original graph and its weakening. -/
theorem insert_allLabels (P : Primitive → Prop) {d I A B}
    (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    AllLabels P (insert G s) ↔ AllLabels P G ∧ P (.weakening s) := by
  constructor
  · intro all
    refine ⟨fun e => all ⟨false,e⟩, ?_⟩
    cases d <;> exact all ⟨true,(0 : Fin 1)⟩
  · rintro ⟨all,weak⟩ ⟨b,e⟩
    cases b
    · exact all e
    · exact Translation.allLabels_primitive P d _ weak e

theorem extend_allLabels (P : Primitive → Prop) {d I k h}
    (G : Hypernet d I (environmentInterface k h)) (s : ShareSort) :
    AllLabels P (extend G s) ↔ AllLabels P G ∧ P (.weakening s) :=
  insert_allLabels P G s

theorem body_allLabels (P : Primitive → Prop) {d n k h}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (s : ShareSort) :
    AllLabels P (body G s) ↔ AllLabels P G ∧ P (.weakening s) :=
  extend_allLabels P G s

theorem left_allLabels (P : Primitive → Prop) {d n k h}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (s : ShareSort) :
    AllLabels P (left G s) ↔ AllLabels P G ∧ P (.weakening s) := by
  constructor
  · intro all; exact (body_allLabels P G s).mp (all (0 : Fin 1))
  · intro all e; exact (body_allLabels P G s).mpr all

theorem right_allLabels (P : Primitive → Prop) {d n k h}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (s : ShareSort) :
    AllLabels P (right G s) ↔ AllLabels P G ∧ P (.weakening s) := by
  rw [right,extend_allLabels]
  constructor
  · rintro ⟨all,weak⟩; exact ⟨all (0 : Fin 1),weak⟩
  · rintro ⟨all,weak⟩; exact ⟨fun _ => all,weak⟩

theorem Step.focusFree {d I O} {G H : Hypernet d I O} (step : Step G H) :
    FocusFree G ∧ FocusFree H := by
  cases step with
  | pull B s free =>
    exact ⟨(left_allLabels _ B s).mpr ⟨free,by intro m eq; cases eq⟩,
      (right_allLabels _ B s).mpr ⟨free,by intro m eq; cases eq⟩⟩

theorem Step.allLabels (P : Primitive → Prop) {d I O} {G H : Hypernet d I O}
    (step : Step G H) : AllLabels P G ↔ AllLabels P H := by
  cases step with
  | pull B s _ => exact (left_allLabels P B s).trans (right_allLabels P B s).symm

theorem UpToIso.focusFree {d I O} {G H : Hypernet d I O} (pair : UpToIso G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.focusFree.1,
      (allLabels_iso_iff _ g).mp step.focusFree.2⟩

theorem UpToIso.allLabels (P : Primitive → Prop) {d I O} {G H : Hypernet d I O}
    (pair : UpToIso G H) : AllLabels P G ↔ AllLabels P H := by
  cases pair with
  | witness f step g =>
    exact (allLabels_iso_iff _ f).trans ((step.allLabels P).trans (allLabels_iso_iff _ g))

/-- The actual pre-template contains the literal box-weakening graph pairs. -/
def template : PreTemplate where
  Rel := UpToIso
  focus_free pair := pair.focusFree

theorem literal {d n k h} (G : Hypernet d [.term] (environmentInterface (n+k) h))
    (s : ShareSort) (free : FocusFree G) : template.Rel (left G s) (right G s) :=
  .witness (DeepIso.refl _) (.pull G s free) (DeepIso.refl _)

end Hypernets.Copying.BoxPullWeakening

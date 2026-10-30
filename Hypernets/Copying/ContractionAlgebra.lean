import Hypernets.Copying.TemplateInputSafety
import Hypernets.Copying.MinimalContractionSpine

/-! The literal ordered contraction-associativity and commutativity pairs of
Figure 21, for both sharing sorts. No input is silently permuted in an
isomorphism: the crossing in commutativity is an actual ordered incidence. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionAlgebra
open Graph

/-- The three-input associativity graph. `false` is `((0,1),2)` and `true`
is `(0,(1,2))`; both have the same ordered boundary `[0,1,2]`. -/
@[reducible] def assocNet (s : ShareSort) (right : Bool) :
    Net primitiveSignature (List.replicate 3 s.wire) [s.wire] where
  Internal := Fin 1
  Edge := Bool
  finiteInternal := Enumeration.fin 1
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel _ := s.wire
  edgeLabel _ := .contraction s
  source e := if right then
      (if e then [.input ⟨0,by simp⟩,.internal 0] else [.input ⟨1,by simp⟩,.input ⟨2,by simp⟩])
    else (if e then [.internal 0,.input ⟨2,by simp⟩] else [.input ⟨0,by simp⟩,.input ⟨1,by simp⟩])
  target e := if e then [.output 0] else [.internal 0]
  source_nodup e := by cases right <;> cases e <;> simp
  target_nodup e := by cases e <;> simp
  source_unique := by
    intro v e f a b
    cases right <;> cases e <;> cases f <;> simp_all
    all_goals rcases a with rfl | rfl <;> simp_all
  target_unique := by
    intro v e f a b
    cases e <;> cases f <;> simp_all
  source_coverage v := by
    cases v with
    | internal i =>
      have eq : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      cases right <;> simp [Port.IsOutput]
    | input i =>
      have choices : i = ⟨0,by simp⟩ ∨ i = ⟨1,by simp⟩ ∨ i = ⟨2,by simp⟩ := by
        have bound : i.val < 3 := by simpa only [List.length_replicate] using i.isLt
        by_cases h : i.val = 0
        · exact .inl (Fin.ext h)
        by_cases k : i.val = 1
        · exact .inr (.inl (Fin.ext k))
        exact .inr (.inr (Fin.ext (by change i.val = 2; omega)))
      rcases choices with rfl | rfl | rfl <;> cases right <;> simp [Port.IsOutput]
    | output i => cases right <;> simp [Port.IsOutput]
  target_coverage v := by
    cases v with
    | internal i =>
      have eq : i = 0 := Fin.ext (by have := i.isLt; omega)
      subst i
      simp [Port.IsInput]
    | input i => simp [Port.IsInput]
    | output i =>
      have eq : i = ⟨0,by simp⟩ := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
      subst i
      simp [Port.IsInput]
  source_typed e := by cases right <;> cases e <;> rfl
  target_typed e := by cases e <;> rfl

/-- The two concrete associations are genuine finite contraction trees. -/
def assocTree (s : ShareSort) (right : Bool) : ContractionTree s 3 where
  net := assocNet s right
  labels _ := .inr rfl
  acyclic path := Net.path_nodup_of_rank (assocNet s right) (fun (b : Bool) => if b then 1 else 0)
    (by
      intro e f adj
      obtain ⟨v,a,b⟩ := adj
      cases right <;> cases e <;> cases f <;> simp_all [assocNet]) path

/-- The two ordered single-contraction graphs. The `true` graph connects the
first external input to the second source port and conversely. -/
def commTree (s : ShareSort) (swapped : Bool) : ContractionTree s 2 :=
  ContractionSpine.tree s 0 (fun _ => swapped)

def assocLeft (d : Nat) (s : ShareSort) := (assocTree s false).atDepth d
def assocRight (d : Nat) (s : ShareSort) := (assocTree s true).atDepth d
def commLeft (d : Nat) (s : ShareSort) := (commTree s true).atDepth d
def commRight (d : Nat) (s : ShareSort) := (commTree s false).atDepth d

/-- The two literal schema names keep independent pre-templates. -/
inductive Kind where
  | associativity | commutativity
  deriving DecidableEq

inductive Step : Kind → {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | assoc (d : Nat) (s : ShareSort) : Step .associativity (assocLeft d s) (assocRight d s)
  | comm (d : Nat) (s : ShareSort) : Step .commutativity (commLeft d s) (commRight d s)

inductive UpToIso (kind : Kind) : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Prop where
  | witness {d I O} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step kind A B) (right : DeepIso B H) : UpToIso kind G H

/-- Literal sharing-only graphs contain no focus, at any allowance. -/
theorem tree_focusFree {s m} (T : ContractionTree s m) (d : Nat) : FocusFree (T.atDepth d) := by
  intro e
  rcases T.labels e with h | h
  all_goals cases d <;> simp_all [ContractionTree.atDepth, primitiveLabel, LabelAll]

theorem Step.focusFree {kind d I O} {G H : Hypernet d I O} (step : Step kind G H) :
    FocusFree G ∧ FocusFree H := by
  cases step with
  | assoc d s => exact ⟨tree_focusFree _ _,tree_focusFree _ _⟩
  | comm d s => exact ⟨tree_focusFree _ _,tree_focusFree _ _⟩

theorem UpToIso.focusFree {kind d I O} {G H : Hypernet d I O} (pair : UpToIso kind G H) :
    FocusFree G ∧ FocusFree H := by
  cases pair with
  | witness f step g => exact ⟨(allLabels_iso_iff _ f).mpr step.focusFree.1,
      (allLabels_iso_iff _ g).mp step.focusFree.2⟩

/-- The exact paper schema up to ordered recursive carrier isomorphism. -/
def template (kind : Kind) : PreTemplate where
  Rel := UpToIso kind
  focus_free pair := pair.focusFree

theorem assoc_literal (d : Nat) (s : ShareSort) :
    (template .associativity).Rel (assocLeft d s) (assocRight d s) :=
  .witness (DeepIso.refl _) (.assoc d s) (DeepIso.refl _)

theorem comm_literal (d : Nat) (s : ShareSort) :
    (template .commutativity).Rel (commLeft d s) (commRight d s) :=
  .witness (DeepIso.refl _) (.comm d s) (DeepIso.refl _)

end Hypernets.Copying.ContractionAlgebra

import Hypernets.Copying.Plugging
import Hypernets.Copying.RecursiveIso

/-! Global label predicates and a precise closure-under-plugging interface. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Lift a primitive-label property through every box, not only outer labels. -/
def LabelAll (P : Primitive → Prop) : (d : Nat) → (alphabet d).Symbol → Prop
  | 0, p => P p.down
  | _+1, .inl p => P p
  | n+1, .inr b => ∀ e, LabelAll P n (b.body.edgeLabel e)

def AllLabels (P : Primitive → Prop) {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e, LabelAll P d (G.edgeLabel e)

def FocusFree {d I O} (G : Hypernet d I O) : Prop :=
  AllLabels (fun p => ∀ m, p ≠ .focus m) G

def HoleFree {d I O} (G : Hypernet d I O) : Prop :=
  AllLabels (fun p => ∀ h, p ≠ .hole h) G

/-- Predicate closure under arbitrary well-typed addressed replacement.
This is stronger than closure only at holes and is useful for label predicates. -/
def ClosedUnderReplacement (C : ∀ {d I O}, Hypernet d I O → Prop) : Prop :=
  ∀ {d I O} {G : Hypernet d I O} {r J K} (s : Site G r J K)
    (H : Hypernet r J K), C G → C H → C (plugAt s H)

/-- Replacing graphs whose every primitive satisfies P preserves P at all depths. -/
theorem allLabels_plugAt (P : Primitive → Prop) : ClosedUnderReplacement (AllLabels P) := by
  intro d I O G r J K s H gf hf
  induction s with
  | shallow C e =>
    intro x
    cases x with
    | inl x => exact gf x.val
    | inr x => exact hf x
  | @inside d I O G e b label r J K s ih =>
    have bf : AllLabels P b.body := by
      have h := gf e
      rw [label] at h
      exact h
    intro x
    classical
    change LabelAll P (d+1) (if x = e then
      .inr ⟨b.bound,b.freeVariables,b.freeAtoms,plugAt s H⟩ else G.edgeLabel x)
    by_cases eq : x = e
    · subst x
      simpa [LabelAll, AllLabels] using ih H bf hf
    · simpa [eq] using gf x

theorem focusFree_closed : ClosedUnderReplacement (fun G => FocusFree G) :=
  allLabels_plugAt _

theorem holeFree_closed : ClosedUnderReplacement (fun G => HoleFree G) :=
  allLabels_plugAt _

/-- A primitive-label property is independent of unused representation allowance. -/
theorem allLabels_raise_iff (P : Primitive → Prop) (d : Nat) {I O} (G : Hypernet d I O) :
    AllLabels P (raise d G) ↔ AllLabels P G := by
  induction d generalizing I O with
  | zero => rfl
  | succ d ih =>
    change (∀ e : G.Edge, LabelAll P (d+2) ((raise (d+1) G).edgeLabel e)) ↔ _
    apply forall_congr'
    intro e
    cases h : G.edgeLabel e with
    | inl p => simp [raise, Net.relabel, h, LabelAll]
    | inr b =>
      change LabelAll P (d+2) (match G.edgeLabel e with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩) ↔ _
      rw [h]
      exact ih b.body

/-- Recursive graph renaming preserves and reflects global label properties. -/
theorem labelAll_equiv (P : Primitive → Prop) (d : Nat)
    {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    LabelAll P d a ↔ LabelAll P d b := by
  induction d with
  | zero => cases h; rfl
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b => cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies rel =>
          obtain ⟨f⟩ := rel
          constructor
          · intro free e
            have := (ih (f.edge_label (f.edges.invFun e))).mp (free _)
            simpa [f.edges.right_inv] using this
          · intro free e
            exact (ih (f.edge_label e)).mpr (free _)

theorem allLabels_iso_iff (P : Primitive → Prop) {d I O} {G H : Hypernet d I O}
    (f : DeepIso G H) : AllLabels P G ↔ AllLabels P H := by
  constructor
  · intro free e
    have := (labelAll_equiv P d (f.edge_label (f.edges.invFun e))).mp (free _)
    simpa [f.edges.right_inv] using this
  · intro free e
    exact (labelAll_equiv P d (f.edge_label e)).mpr (free _)
end Hypernets.Copying

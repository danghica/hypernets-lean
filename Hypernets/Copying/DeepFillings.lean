import Hypernets.Copying.OneWay

/-! Related holes at arbitrary box depth, with structural filling certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

/-- A depth-indexed pre-template has actual graph pairs and global focus freedom. -/
structure PreTemplate where
  Rel : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop
  focus_free : ∀ {d I O} {G H : Hypernet d I O}, Rel G H → FocusFree G ∧ FocusFree H

def PreTemplate.OutputClosed (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → OneWay G ∨ OneWay H

/-- A literal labelled corolla, with arbitrary names but no additional edges. -/
structure LabelCopy {d I O} (G : Hypernet d I O) (label : (alphabet d).Symbol) where
  edge : G.Edge
  edge_label : G.edgeLabel edge = label
  source : G.source edge = (List.finRange I.length).map Port.input
  target : G.target edge = (List.finRange O.length).map Port.output
  only : ∀ x, x = edge

def LabelCopy.corolla {d} (label : (alphabet d).Symbol) :
    LabelCopy (Net.corolla (alphabet d).signature label) label :=
  ⟨0,rfl,rfl,rfl,fun x => Fin.ext (by have h := x.isLt; omega)⟩

theorem LabelCopy.focusFree {d I O} {G : Hypernet d I O} {label}
    (c : LabelCopy G label) (free : LabelAll (fun p => ∀ m, p ≠ .focus m) d label) : FocusFree G := by
  intro x; rw [c.only x,c.edge_label]; exact free

def LabelCopy.retained {d I O} {C : Hypernet d I O} {H e}
    (c : LabelCopy (H e) (C.edgeLabel e)) : Retained C H e where
  edge := c.edge
  primitive p := by rw [c.edge_label]
  source := c.source
  target := c.target
  only := c.only

theorem LabelCopy.oneWay {d I O} {G : Hypernet d I O} {label}
    (c : LabelCopy G label) (nonop : ∀ o, label ≠ primitiveLabel d (.operation o)) : OneWay G := by
  intro j _ reach
  apply reach.not_nonoperation_target (e := c.edge)
  · intro o; rw [c.edge_label]; exact nonop o
  · rw [c.target]; exact List.mem_map_of_mem (List.mem_finRange j)

mutual
inductive DeepFilling (T : PreTemplate) : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Hypernet d I O → Prop where
  | expand {d I O} (C : Hypernet d I O)
      (H K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e)))
      (edges : ∀ e, DeepFillingEdge T C H K e) : DeepFilling T C (C.expand H) (C.expand K)

/-- Replacement descends through original boxes only, never through a newly filled hole. -/
inductive DeepFillingEdge (T : PreTemplate) : {d : Nat} → {I O : List Wire} → (C : Hypernet d I O) →
    ((e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) →
    ((e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) → C.Edge → Prop where
  | retained {d I O} {C : Hypernet d I O} {H K e} :
      LabelCopy (H e) (C.edgeLabel e) → LabelCopy (K e) (C.edgeLabel e) → DeepFillingEdge T C H K e
  | filled {d I O} {C : Hypernet d I O} {H K e} (h : Hole) :
      C.edgeLabel e = primitiveLabel d (.hole h) → T.Rel (H e) (K e) → DeepFillingEdge T C H K e
  | boxed {d I O} {C : Hypernet (d+1) I O} {H K e}
      (b : Box (alphabet d)) (label : C.edgeLabel e = .inr b)
      {L R : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)}
      (inner : DeepFilling T b.body L R)
      (left : LabelCopy (d := d+1) (H e) (.inr ⟨b.bound,b.freeVariables,b.freeAtoms,L⟩))
      (right : LabelCopy (d := d+1) (K e) (.inr ⟨b.bound,b.freeVariables,b.freeAtoms,R⟩)) : DeepFillingEdge T C H K e
end

/-- Both fillings preserve global focus freedom, including every rebuilt box. -/
theorem DeepFilling.focusFree {T d I O} {C L R : Hypernet d I O}
    (h : DeepFilling T C L R) (free : FocusFree C) : FocusFree L ∧ FocusFree R := by
  induction d generalizing I O with
  | zero =>
    cases h with
    | expand C H K edges =>
      have each (e : C.Edge) : FocusFree (H e) ∧ FocusFree (K e) := by
        cases edges e with
        | retained l r => exact ⟨l.focusFree (free e),r.focusFree (free e)⟩
        | filled h label rel => exact T.focus_free rel
      exact ⟨fun ⟨e,x⟩ => (each e).1 x,fun ⟨e,x⟩ => (each e).2 x⟩
  | succ d ih =>
    cases h with
    | expand C H K edges =>
      have each (e : C.Edge) : FocusFree (H e) ∧ FocusFree (K e) := by
        cases edges e with
        | retained l r => exact ⟨l.focusFree (free e),r.focusFree (free e)⟩
        | filled h label rel => exact T.focus_free rel
        | boxed b label inner l r =>
          have bf : FocusFree b.body := by have f := free e; rw [label] at f; exact f
          have fills := ih inner bf
          exact ⟨l.focusFree fills.1,r.focusFree fills.2⟩
      exact ⟨fun ⟨e,x⟩ => (each e).1 x,fun ⟨e,x⟩ => (each e).2 x⟩

/-- A rebuilt box is retained for outer search: its body cannot be inspected there. -/
def LabelCopy.retainedBox {d I O} {C : Hypernet (d+1) I O} {H e}
    {b a : Box (alphabet d)} (label : C.edgeLabel e = .inr b)
    (c : LabelCopy (d := d+1) (H e) (.inr a)) : Retained C H e where
  edge := c.edge
  primitive p := by rw [c.edge_label,label]; simp [primitiveLabel]
  source := c.source
  target := c.target
  only := c.only

/-- Every outer interaction either belongs to an actual template hole or is retained. -/
theorem DeepFillingEdge.origin {T d I O} {C : Hypernet d I O} {H K e}
    (cert : DeepFillingEdge T C H K e) :
    (Nonempty (Retained C H e) ∧ Nonempty (Retained C K e)) ∨
      ∃ h, C.edgeLabel e = primitiveLabel d (.hole h) ∧ T.Rel (H e) (K e) := by
  cases cert with
  | retained l r => exact .inl ⟨⟨l.retained⟩,⟨r.retained⟩⟩
  | filled h label rel => exact .inr ⟨h,label,rel⟩
  | boxed b label inner l r => exact .inl ⟨⟨l.retainedBox label⟩,⟨r.retainedBox label⟩⟩

/-- All search-preservation and reflection premises are proved from graph certificates. -/
theorem deepFilling_search {T d I O} {C : Hypernet d I O} {H K}
    (edges : ∀ e, DeepFillingEdge T C H K e) :
    Preserves C H ∧ Preserves C K ∧ Origins C H ∧ Origins C K := by
  have preserve : Preserves C H ∧ Preserves C K := by
    constructor <;> intro e p label interactive
    all_goals
      rcases (edges e).origin with copies | ⟨h,hole,_⟩
      · first | exact copies.1 | exact copies.2
      · have eq := primitiveLabel_injective d (label.symm.trans hole)
        subst p; simp [Search.Interactive] at interactive
  refine ⟨preserve.1,preserve.2,?_,?_⟩
  all_goals
    intro e x p label interactive
    rcases (edges e).origin with copies | ⟨h,hole,_⟩
    · first | exact .inl copies.1 | exact .inl copies.2
    · exact .inr ⟨h,hole⟩

/-- Retained holes themselves are one-way, so output closure needs no requirement
that every original hole is filled in the same outer expansion. -/
theorem deepFilling_outputClosed {T d I O} {C : Hypernet d I O} {H K}
    (edges : ∀ e, DeepFillingEdge T C H K e) (closed : T.OutputClosed) : OutputClosedPair C H K := by
  intro e h hole
  cases edges e with
  | retained l r => exact .inl (l.oneWay (by intro o; rw [hole]; intro eq; cases primitiveLabel_injective d eq))
  | filled h label rel => exact closed rel
  | boxed b label inner l r => rw [label] at hole; cases hole
end Hypernets.Copying

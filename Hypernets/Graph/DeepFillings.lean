import Hypernets.Graph.ShallowSpecimens
import Hypernets.Graph.ExpansionCopies

/-! Recursive paired fillings: related holes, retained edges, and filled box bodies. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- A single-edge graph with full ordered boundary incidence and a specified label.
Unlike CorollaCopy, the label may describe an updated box body. -/
structure LabelCopy {d I O} (G : Hypernet ops d I O) (label : (alphabet ops d).Symbol) where
  edge : G.Edge
  edge_label : G.edgeLabel edge = label
  source : G.source edge = (List.finRange I.length).map Port.input
  target : G.target edge = (List.finRange O.length).map Port.output
  only : ∀ x, x = edge

def LabelCopy.corolla {d} (label : (alphabet ops d).Symbol) :
    LabelCopy (Net.corolla (alphabet ops d).signature label) label :=
  ⟨0,rfl,rfl,rfl,fun x => Fin.ext (by have h := x.isLt; omega)⟩

theorem LabelCopy.focusFree {d I O} {G : Hypernet ops d I O}
    {label : (alphabet ops d).Symbol} (copy : LabelCopy G label)
    (free : LabelFocusFree ops d label) : FocusFree G := by
  intro x
  rw [copy.only x,copy.edge_label]
  exact free

/-- A non-operation corolla cannot carry an operation path to a term output. -/
theorem LabelCopy.oneWay {d I O} {G : Hypernet ops d I O}
    {label : (alphabet ops d).Symbol} (copy : LabelCopy G label)
    (nonop : ¬ IsOperation ops d label) : OneWay G := by
  apply oneWay_iff.mpr
  intro j _ reach
  have mem : Port.output j ∈ G.target copy.edge := by
    rw [copy.target]
    exact List.mem_map_of_mem (List.mem_finRange j)
  have op := reach.incoming_operation mem
  rw [copy.edge_label] at op
  exact nonop op

/-- One concrete pre-template for each available depth bound. Compatibility
between different bounds remains a separate representation question. -/
abbrev LayeredPreTemplate (ops : Operations Op) := (d : Nat) → ConcretePreTemplate ops d

mutual
/-- A finite recursive certificate for actual paired graph fillings.
Recursion descends only through original box bodies, not inserted replacements. -/
inductive DeepFilling (T : LayeredPreTemplate ops) :
    {d : Nat} → {I O : List Wire} →
    Hypernet ops d I O → Hypernet ops d I O → Hypernet ops d I O → Prop where
  | expand {d I O} (C : Hypernet ops d I O)
      (H K : (e : C.Edge) → Hypernet ops d
        ((alphabet ops d).signature.input (C.edgeLabel e))
        ((alphabet ops d).signature.output (C.edgeLabel e)))
      (edges : ∀ e, DeepFillingEdge T C H K e) :
      DeepFilling T C (C.expand H) (C.expand K)

/-- Each edge is retained, filled at a hole, or rebuilt as a box whose body
has a recursively certified paired filling. No path or boundary law is assumed. -/
inductive DeepFillingEdge (T : LayeredPreTemplate ops) :
    {d : Nat} → {I O : List Wire} → (C : Hypernet ops d I O) →
    ((e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) →
    ((e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) → C.Edge → Prop where
  | retained {d I O C H K e} :
      ExpansionPaths.CorollaCopy (ops := ops) (d := d) (I := I) (O := O) C H e →
      ExpansionPaths.CorollaCopy C K e → DeepFillingEdge T C H K e
  | filled {d I O C H K e} (h : Hole) :
      C.edgeLabel e = primitiveLabel ops d (.hole h) →
      (T d).Rel (I := (alphabet ops d).signature.input (C.edgeLabel e))
        (O := (alphabet ops d).signature.output (C.edgeLabel e)) (H e) (K e) →
      DeepFillingEdge T (I := I) (O := O) C H K e
  | boxed {d I O} {C : Hypernet ops (d+1) I O} {H K e}
      (b : Box (alphabet ops d)) (label : C.edgeLabel e = .inr b)
      {L R : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term)}
      (inner : DeepFilling T b.body L R)
      (left : LabelCopy (ops := ops) (d := d+1) (H e) (.inr ⟨b.bound,b.free,L⟩))
      (right : LabelCopy (ops := ops) (d := d+1) (K e) (.inr ⟨b.bound,b.free,R⟩)) :
      DeepFillingEdge T C H K e
end

/-- The previous shallow representation embeds as a special case. -/
theorem SpecimenEdge.deep {d I O} {T : LayeredPreTemplate ops}
    {C : Hypernet ops d I O} {H K e} (h : SpecimenEdge (T d) C H K e) :
    DeepFillingEdge T C H K e := by
  cases h with
  | retained l r => exact .retained l r
  | filled h label rel => exact .filled h label rel

/-- Recursive filling preserves global absence of focuses on both sides. -/
theorem DeepFilling.focusFree {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} (h : DeepFilling T C L R) (free : FocusFree C) :
    FocusFree L ∧ FocusFree R := by
  induction d generalizing I O with
  | zero =>
    cases h with
    | expand C H K edges =>
      have each (e : C.Edge) : FocusFree (H e) ∧ FocusFree (K e) := by
        cases edges e with
        | retained l r => exact ⟨ExpansionPaths.copy_focusFree _ _ l (free e),
            ExpansionPaths.copy_focusFree _ _ r (free e)⟩
        | filled h label rel => exact (T 0).focus_free rel
      exact ⟨fun ⟨e,x⟩ => (each e).1 x,fun ⟨e,x⟩ => (each e).2 x⟩
  | succ d ih =>
    cases h with
    | expand C H K edges =>
      have each (e : C.Edge) : FocusFree (H e) ∧ FocusFree (K e) := by
        cases edges e with
        | retained l r => exact ⟨ExpansionPaths.copy_focusFree _ _ l (free e),
            ExpansionPaths.copy_focusFree _ _ r (free e)⟩
        | filled h label rel => exact (T (d+1)).focus_free rel
        | boxed b label inner l r =>
            have bf : FocusFree b.body := by
              have h := free e
              rw [label] at h
              exact h
            have fills := ih inner bf
            exact ⟨l.focusFree fills.1,r.focusFree fills.2⟩
      exact ⟨fun ⟨e,x⟩ => (each e).1 x,fun ⟨e,x⟩ => (each e).2 x⟩

/-- Focus freedom for a particular original label suffices for its fillings. -/
theorem DeepFillingEdge.focusFree {T : LayeredPreTemplate ops} {d I O}
    {C : Hypernet ops d I O} {H K e} (h : DeepFillingEdge T C H K e)
    (free : LabelFocusFree ops d (C.edgeLabel e)) : FocusFree (H e) ∧ FocusFree (K e) := by
  cases h with
  | retained l r => exact ⟨ExpansionPaths.copy_focusFree _ _ l free,
      ExpansionPaths.copy_focusFree _ _ r free⟩
  | filled h label rel => exact (T _).focus_free rel
  | boxed b label inner l r =>
      rw [label] at free
      have fills := inner.focusFree free
      exact ⟨l.focusFree fills.1,r.focusFree fills.2⟩

/-- A unique shallow focus is necessarily retained, never replaced as a hole or box. -/
theorem DeepFillingEdge.focus_copies {T : LayeredPreTemplate ops} {d I O}
    {C : Hypernet ops d I O} {H K} (f : Focussed C)
    (h : DeepFillingEdge T C H K f.edge) :
    Nonempty (ExpansionPaths.CorollaCopy C H f.edge × ExpansionPaths.CorollaCopy C K f.edge) := by
  cases h with
  | retained l r => exact ⟨l,r⟩
  | filled h label rel => exact False.elim (focusLabel_ne_hole f.mode h (f.label.symm.trans label))
  | boxed b label inner l r =>
      have eq := f.label.symm.trans label
      cases eq

/-- Output closure at holes and non-operation box copies give the pointwise
hypothesis for paired path reflection in the original outer context. -/
theorem DeepFillingEdge.outputClosed {T : LayeredPreTemplate ops} {d I O}
    {C : Hypernet ops d I O} {H K e} (h : DeepFillingEdge T C H K e)
    (closed : (T d).OutputClosed) :
    (Nonempty (ExpansionPaths.CorollaCopy C H e) ∧ Nonempty (ExpansionPaths.CorollaCopy C K e)) ∨
      OneWay (H e) ∨ OneWay (K e) := by
  cases h with
  | retained l r => exact .inl ⟨⟨l⟩,⟨r⟩⟩
  | filled h label rel => exact .inr (closed rel)
  | boxed b label inner l r => exact .inr (.inl (l.oneWay (by simp [IsOperation])))

end Hypernets.Linear

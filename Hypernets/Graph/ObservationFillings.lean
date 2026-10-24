import Hypernets.Graph.InitialObservations

/-! Template-independent recursive substitution for contextual observations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Linear.ObservationFillings
open Graph
variable {Op : Type} {ops : Operations Op}

/-- A typed set of substitution slots, indexed by depth and hole signature. -/
abbrev Slots := Nat → Hole → Prop

/-- A fragment vector supplies a graph independently at every declared slot. -/
abbrev Fragments (slots : Slots) := ∀ n h, slots n h → Hypernet ops n h.input h.output

mutual
/-- Every hole in the original context has a declared substitution slot. -/
def Covers (slots : Slots) : {n : Nat} → {I O : List Wire} → Hypernet ops n I O → Prop
  | _,_,_,C => ∀ e, CoversLabel slots _ (C.edgeLabel e)
def CoversLabel (slots : Slots) : (n : Nat) → (alphabet ops n).Symbol → Prop
  | 0, .up (.hole h) => slots 0 h
  | 0, .up _ => True
  | n+1, .inl (.hole h) => slots (n+1) h
  | _+1, .inl _ => True
  | n+1, .inr b => Covers slots b.body
end

theorem Covers.edge {slots : Slots} {n I O} {C : Hypernet ops n I O}
    (h : Covers slots C) (e : C.Edge) : CoversLabel slots n (C.edgeLabel e) := by
  exact (show ∀ e, CoversLabel slots n (C.edgeLabel e) from by simpa only [Covers] using h) e

mutual
/-- Substitute original holes once and recurse only through original boxes. -/
noncomputable def fill {slots : Slots} (a : Fragments (ops := ops) slots) :
    {n : Nat} → {I O : List Wire} → (C : Hypernet ops n I O) → Covers slots C → Hypernet ops n I O
  | _,_,_,C,h => C.expand (fun e => fillLabel a _ (C.edgeLabel e) (h.edge e))
noncomputable def fillLabel {slots : Slots} (a : Fragments (ops := ops) slots) :
    (n : Nat) → (p : (alphabet ops n).Symbol) → CoversLabel slots n p →
      Hypernet ops n ((alphabet ops n).signature.input p) ((alphabet ops n).signature.output p)
  | 0, .up (.hole h), w => a 0 h (by simpa only [CoversLabel] using w)
  | 0, .up (.operation o), _ => Net.corolla (alphabet ops 0).signature (.up (.operation o))
  | 0, .up .variable, _ => Net.corolla (alphabet ops 0).signature (.up .variable)
  | 0, .up (.focus m), _ => Net.corolla (alphabet ops 0).signature (.up (.focus m))
  | n+1, .inl (.hole h), w => a (n+1) h (by simpa only [CoversLabel] using w)
  | n+1, .inl (.operation o), _ => Net.corolla (alphabet ops (n+1)).signature (.inl (.operation o))
  | n+1, .inl .variable, _ => Net.corolla (alphabet ops (n+1)).signature (.inl .variable)
  | n+1, .inl (.focus m), _ => Net.corolla (alphabet ops (n+1)).signature (.inl (.focus m))
  | n+1, .inr b, w => Net.corolla (alphabet ops (n+1)).signature (.inr ⟨b.bound,b.free,fill a b.body (by simpa only [CoversLabel] using w)⟩)
end

/-- Pointwise template membership of the independently supplied fragments. -/
def Related (T : LayeredPreTemplate ops) {slots : Slots} (a b : Fragments (ops := ops) slots) : Prop :=
  ∀ n h (w : slots n h), (T n).Rel (a n h w) (b n h w)

/-- A label copy at an edge supplies the retained-corolla certificate. -/
def retainedCopy {n I O} {C : Hypernet ops n I O} {H} {e : C.Edge}
    (copy : LabelCopy (H e) (C.edgeLabel e)) : ExpansionPaths.CorollaCopy C H e :=
  ⟨copy.edge,copy.edge_label,copy.source,copy.target,copy.only⟩

/-- Local paired substitution, expressed without a surrounding edge family. -/
inductive PairedLabel (T : LayeredPreTemplate ops) : (n : Nat) →
    (p : (alphabet ops n).Symbol) →
    Hypernet ops n ((alphabet ops n).signature.input p) ((alphabet ops n).signature.output p) →
    Hypernet ops n ((alphabet ops n).signature.input p) ((alphabet ops n).signature.output p) → Prop where
  | retained {n p G H} : LabelCopy G p → LabelCopy H p → PairedLabel T n p G H
  | filled {n p G H} (h : Hole) : p = primitiveLabel ops n (.hole h) → (T n).Rel G H → PairedLabel T n p G H
  | boxed {n p} (b : Box (alphabet ops n)) (label : p = .inr b) {L R}
      {G H : Hypernet ops (n+1) ((alphabet ops (n+1)).signature.input p) ((alphabet ops (n+1)).signature.output p)} :
      DeepFilling T b.body L R →
      LabelCopy G (.inr ⟨b.bound,b.free,L⟩) → LabelCopy H (.inr ⟨b.bound,b.free,R⟩) →
      PairedLabel T (n+1) p G H

/-- Local certificates become the existing recursive edge certificates. -/
theorem PairedLabel.edge {T : LayeredPreTemplate ops} {n I O} {C : Hypernet ops n I O} {H K} {e : C.Edge}
    (h : PairedLabel T n (C.edgeLabel e) (H e) (K e)) : DeepFillingEdge T C H K e := by
  cases h with
  | retained l r => exact .retained (retainedCopy l) (retainedCopy r)
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner l r

/-- Independently substituted labels are paired, including nested original boxes. -/
theorem paired_label (T : LayeredPreTemplate ops) {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) (n : Nat) (p : (alphabet ops n).Symbol) (h : CoversLabel slots n p) :
    PairedLabel T n p (fillLabel a n p h) (fillLabel b n p h) := by
  induction n with
  | zero =>
    cases p with
    | up p =>
      cases p with
      | hole hole => simpa only [fillLabel, primitiveLabel] using PairedLabel.filled hole rfl (rel 0 hole (by simpa only [CoversLabel] using h))
      | operation o => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
      | «variable» => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
      | focus m => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
  | succ n ih =>
    cases p with
    | inl p =>
      cases p with
      | hole hole => simpa only [fillLabel, primitiveLabel] using PairedLabel.filled hole rfl (rel (n+1) hole (by simpa only [CoversLabel] using h))
      | operation o => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
      | «variable» => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
      | focus m => simpa only [fillLabel] using PairedLabel.retained (LabelCopy.corolla _) (LabelCopy.corolla _)
    | inr box =>
      have cover : Covers slots box.body := by simpa only [CoversLabel] using h
      have inner : DeepFilling T box.body (fill a box.body cover) (fill b box.body cover) := by
        rw [fill,fill]
        exact .expand _ _ _ (fun e => (ih (box.body.edgeLabel e) (cover.edge e)).edge)
      simpa only [fillLabel] using PairedLabel.boxed box rfl inner (LabelCopy.corolla _) (LabelCopy.corolla _)

/-- Related vectors yield paired certificates at every original edge. -/
theorem paired_edges (T : LayeredPreTemplate ops) {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) {n I O} (C : Hypernet ops n I O) (h : Covers slots C) :
    ∀ e, DeepFillingEdge T C (fun e => fillLabel a n (C.edgeLabel e) (h.edge e))
      (fun e => fillLabel b n (C.edgeLabel e) (h.edge e)) e :=
  fun e => (paired_label T rel n (C.edgeLabel e) (h.edge e)).edge

/-- Independent substitution of related fragments yields a paired recursive filling. -/
theorem paired (T : LayeredPreTemplate ops) {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) {n I O} (C : Hypernet ops n I O) (h : Covers slots C) :
    DeepFilling T C (fill a C h) (fill b C h) := by
  rw [fill,fill]
  exact .expand _ _ _ (paired_edges T rel C h)
/-- Every closed observation of related vectors has a finite exact original-hole
substitution tuple; unused declared slots do not add entries to that tuple. -/
theorem finite_tuple (T : LayeredPreTemplate ops) {slots : Slots} {a b : Fragments (ops := ops) slots}
    (rel : Related T a b) {n I O} (C : Context ops n I O) (h : Covers slots C.val)
    (closed : HoleFree (fill a C.val h)) :
    ∃ entries, TupleFilling T C.val (fill a C.val h) (fill b C.val h) entries ∧
      (entries.map TupleEntry.hole).Nodup ∧
      ∀ hole, hole ∈ entries.map TupleEntry.hole ↔ HasHole C.val hole := by
  obtain ⟨entries,tuple⟩ := (paired T rel C.val h).tuple
  exact ⟨entries,tuple,tuple.inventory C.property closed⟩

end Hypernets.Linear.ObservationFillings

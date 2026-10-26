import Hypernets.Copying.PaddingPredicates

/-! Removing one unused depth allowance. Truncation is an auxiliary total map,
not a machine rule or a term translation. Its dummy holes are unreachable on
graphs satisfying `Fits`; this is proved by the two round-trip theorems. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace Lowering

/-- A typed placeholder makes truncation total even on erased context slots.
It is never used for an actual box in a graph satisfying `Fits` at depth zero. -/
def slot (b : Box (alphabet 0)) : Primitive :=
  .hole ⟨0, [.thunk b.bound], environmentInterface b.freeVariables b.freeAtoms⟩

/-- Auxiliary truncation; one excessive innermost box becomes a typed slot. -/
def lower : (d : Nat) → {I O : List Wire} → Hypernet (d+1) I O → Hypernet d I O
  | 0, _, _, G => G.relabel _
      (fun p => .up (match p with | .inl p => p | .inr b => slot b))
      (by intro p; cases p <;> rfl) (by intro p; cases p <;> rfl)
  | d+1, _, _, G => G.relabel _
      (fun p => match p with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,lower d b.body⟩)
      (by intro p; cases p <;> rfl) (by intro p; cases p <;> rfl)

/-- Uniform label presentation of truncation. -/
def label : (d : Nat) → (alphabet (d+1)).Symbol → (alphabet d).Symbol
  | 0, .inl p => .up p
  | 0, .inr b => .up (slot b)
  | _+1, .inl p => .inl p
  | d+1, .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,lower d b.body⟩

theorem label_input (d : Nat) (a : (alphabet (d+1)).Symbol) :
    (alphabet d).signature.input (label d a) = (alphabet (d+1)).signature.input a := by
  cases d <;> cases a <;> rfl

theorem label_output (d : Nat) (a : (alphabet (d+1)).Symbol) :
    (alphabet d).signature.output (label d a) = (alphabet (d+1)).signature.output a := by
  cases d <;> cases a <;> rfl

/-- Truncation with definitionally unchanged outer carriers and incidence. -/
def graph {d I O} (G : Hypernet (d+1) I O) : Hypernet d I O :=
  G.relabel _ (label d) (label_input d) (label_output d)

theorem graph_eq_lower {d I O} (G : Hypernet (d+1) I O) : graph G = lower d G := by
  cases d <;> unfold graph lower <;> congr 1 <;> funext p <;> cases p <;> rfl

/-- A label can lose one allowance precisely when no box uses its last layer. -/
def FitsLabel : (d : Nat) → (alphabet (d+1)).Symbol → Prop
  | _, .inl _ => True
  | 0, .inr _ => False
  | d+1, .inr b => ∀ e, FitsLabel d (b.body.edgeLabel e)

/-- Every nested box fits in the smaller allowance. -/
def Fits {d I O} (G : Hypernet (d+1) I O) : Prop := ∀ e, FitsLabel d (G.edgeLabel e)

/-- Representability is invariant under independent renaming inside boxes. -/
theorem fitsLabel_equiv (d : Nat) {a b : (alphabet (d+1)).Symbol}
    (h : LabelEquiv (d+1) a b) : FitsLabel d a ↔ FitsLabel d b := by
  induction d with
  | zero =>
    cases a with
    | inl a => cases b with
      | inl b => rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => rfl
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b => rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies related =>
          obtain ⟨f⟩ := related
          constructor
          · intro fit e
            have ht := (ih (f.edge_label (f.edges.invFun e))).mp (fit _)
            simpa only [f.edges.right_inv] using ht
          · intro fit e
            exact (ih (f.edge_label e)).mpr (fit _)

theorem fits_iso_iff {d I O} {G H : Hypernet (d+1) I O} (f : DeepIso G H) :
    Fits G ↔ Fits H := by
  constructor
  · intro h e
    have ht := (fitsLabel_equiv d (f.edge_label (f.edges.invFun e))).mp (h _)
    simpa only [f.edges.right_inv] using ht
  · intro h e
    exact (fitsLabel_equiv d (f.edge_label e)).mpr (h _)

/-- Every actual padding lies in the representable fragment. -/
theorem fits_padding_label (d : Nat) (a : (alphabet d).Symbol) :
    FitsLabel d (Padding.label d a) := by
  induction d with
  | zero => trivial
  | succ d ih =>
    cases a with
    | inl p => trivial
    | inr b =>
      change Fits (raise d b.body)
      rw [← Padding.graph_eq_raise]
      exact fun e => ih _

theorem fits_graph {d I O} (G : Hypernet d I O) : Fits (Padding.graph G) :=
  fun e => fits_padding_label d (G.edgeLabel e)

theorem fits_raise {d I O} (G : Hypernet d I O) : Fits (raise d G) := by
  rw [← Padding.graph_eq_raise]; exact fits_graph G

/-- Truncation preserves recursive label equivalence, even on erased slots. -/
theorem label_equiv (d : Nat) {a b : (alphabet (d+1)).Symbol}
    (h : LabelEquiv (d+1) a b) : LabelEquiv d (label d a) (label d b) := by
  induction d with
  | zero =>
    cases a with
    | inl a => cases b with
      | inl b => change a = b at h; cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => cases h; rfl
  | succ d ih =>
    cases a with
    | inl a => cases b with
      | inl b => exact h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies related =>
          obtain ⟨f⟩ := related
          apply BoxRelated.bodies
          rw [← graph_eq_lower, ← graph_eq_lower]
          exact ⟨{
            vertices := f.vertices
            edges := f.edges
            internal_label := f.internal_label
            edge_label e := ih (f.edge_label e)
            source := f.source
            target := f.target }⟩

/-- Truncation carries the original port and edge bijections unchanged. -/
def graphIso {d I O} {G H : Hypernet (d+1) I O} (f : DeepIso G H) :
    DeepIso (graph G) (graph H) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := label_equiv d (f.edge_label e)
  source := f.source
  target := f.target

/-- Lowering after padding recovers each label up to recursive isomorphism. -/
theorem label_roundtrip (d : Nat) (a : (alphabet d).Symbol) :
    LabelEquiv d (label d (Padding.label d a)) a := by
  induction d with
  | zero => cases a; rfl
  | succ d ih =>
    cases a with
    | inl p => rfl
    | inr b =>
      apply BoxRelated.bodies
      rw [← graph_eq_lower, ← Padding.graph_eq_raise]
      exact ⟨{
        vertices := Bijection.refl _
        edges := Bijection.refl _
        internal_label _ := rfl
        edge_label e := ih _
        source e := by change (b.body.source e).map (Port.map id) = _; simp [Bijection.refl]
        target e := by change (b.body.target e).map (Port.map id) = _; simp [Bijection.refl] }⟩

/-- A genuine left inverse of padding, fixing every outer vertex and edge. -/
def roundtrip {d I O} (G : Hypernet d I O) : DeepIso (graph (Padding.graph G)) G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := label_roundtrip d (G.edgeLabel e)
  source e := by change (G.source e).map (Port.map id) = _; simp [Bijection.refl]
  target e := by change (G.target e).map (Port.map id) = _; simp [Bijection.refl]

/-- A representable label survives lowering followed by padding. -/
theorem label_recover (d : Nat) (a : (alphabet (d+1)).Symbol) (fit : FitsLabel d a) :
    LabelEquiv (d+1) (Padding.label d (label d a)) a := by
  induction d with
  | zero => cases a with
    | inl p => rfl
    | inr b => exact False.elim fit
  | succ d ih =>
    cases a with
    | inl p => rfl
    | inr b =>
      apply BoxRelated.bodies
      rw [← graph_eq_lower, ← Padding.graph_eq_raise]
      exact ⟨{
        vertices := Bijection.refl _
        edges := Bijection.refl _
        internal_label _ := rfl
        edge_label e := ih _ (fit e)
        source e := by change (b.body.source e).map (Port.map id) = _; simp [Bijection.refl]
        target e := by change (b.body.target e).map (Port.map id) = _; simp [Bijection.refl] }⟩

/-- The converse round trip is restricted to actual representable graphs. -/
def recover {d I O} (G : Hypernet (d+1) I O) (fit : Fits G) :
    DeepIso (Padding.graph (graph G)) G where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := label_recover d (G.edgeLabel e) (fit e)
  source e := by change (G.source e).map (Port.map id) = _; simp [Bijection.refl]
  target e := by change (G.target e).map (Port.map id) = _; simp [Bijection.refl]

/-- Representability exactly characterises the isomorphism-closed image of padding. -/
theorem fits_iff_image {d I O} (H : Hypernet (d+1) I O) :
    Fits H ↔ ∃ G : Hypernet d I O, Nonempty (DeepIso (Padding.graph G) H) := by
  constructor
  · intro fit; exact ⟨graph H, ⟨recover H fit⟩⟩
  · rintro ⟨G, ⟨f⟩⟩; exact (fits_iso_iff f).mp (fits_graph G)

/-- Padding is faithful: extra allowance cannot identify previously different graphs. -/
def reflectIso {d I O} {G H : Hypernet d I O}
    (f : DeepIso (Padding.graph G) (Padding.graph H)) : DeepIso G H :=
  (roundtrip G).symm.trans ((graphIso f).trans (roundtrip H))

theorem padding_iso_iff {d I O} (G H : Hypernet d I O) :
    Nonempty (DeepIso (raise d G) (raise d H)) ↔ Nonempty (DeepIso G H) := by
  rw [← Padding.graph_eq_raise, ← Padding.graph_eq_raise]
  constructor
  · rintro ⟨f⟩; exact ⟨reflectIso f⟩
  · rintro ⟨f⟩
    simpa only [Padding.graph_eq_raise] using (show Nonempty (DeepIso (raise d G) (raise d H)) from ⟨Padding.congr f⟩)

end Lowering
end Hypernets.Copying

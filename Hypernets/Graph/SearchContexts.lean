import Hypernets.Graph.ContextualSearch
import Hypernets.Graph.TransportPlug

/-! The selected-edge presentation is an actual focus-free simple hole context. -/
namespace Hypernets.Linear.SearchContexts
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
    (C : Hypernet ops d I O) (e : C.Edge)

section Relabel
variable (l : (alphabet ops d).Symbol)
    (hi : (alphabet ops d).signature.input l = (alphabet ops d).signature.input (C.edgeLabel e))
    (ho : (alphabet ops d).signature.output l = (alphabet ops d).signature.output (C.edgeLabel e))

/-- Change only the discarded slot label, preserving its ordered signature. -/
noncomputable def relabel : Hypernet ops d I O := by
  classical
  exact C.relabelEdges (alphabet ops d).signature (fun x => if x = e then l else C.edgeLabel x)
    (by intro x; by_cases h : x = e <;> simp [h,hi])
    (by intro x; by_cases h : x = e <;> simp [h,ho])

theorem selected_label : (relabel C e l hi ho).edgeLabel e = l := by
  classical
  simp [relabel]

theorem other_label (x : C.Edge) (ne : x ≠ e) :
    (relabel C e l hi ho).edgeLabel x = C.edgeLabel x := by
  classical
  simp [relabel,ne]

/-- The discarded label does not affect the context's graph geometry. -/
noncomputable def geometry : Net.RelIso (fun _ _ => True) C (relabel C e l hi ho) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := trivial
  source _ := by simp [Bijection.refl,relabel,Net.relabelEdges]
  target _ := by simp [Bijection.refl,relabel,Net.relabelEdges]

theorem input_eq : (alphabet ops d).signature.input (C.edgeLabel e) =
    (alphabet ops d).signature.input ((relabel C e l hi ho).edgeLabel e) := by
  rw [selected_label,hi]

theorem output_eq : (alphabet ops d).signature.output (C.edgeLabel e) =
    (alphabet ops d).signature.output ((relabel C e l hi ho).edgeLabel e) := by
  rw [selected_label,ho]

/-- Relabelling the discarded slot commutes with every plugging, not just search patterns. -/
noncomputable def plug_iso
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) :
    Net.Iso (C.plug e H)
      ((relabel C e l hi ho).plug e (H.reboundary (input_eq C e l hi ho) (output_eq C e l hi ho))) := by
  let a := (geometry C e l hi ho).plugHost e (input_eq C e l hi ho) (output_eq C e l hi ho) (fun _ => trivial) H
  exact {
    vertices := a.vertices
    edges := a.edges
    internal_label := a.internal_label
    source := a.source
    target := a.target
    edge_label := by
      intro x
      cases x with
      | inl x => exact other_label C e l hi ho x.val x.property
      | inr x => rfl }

/-- Conversely, every replacement for the relabelled slot can be plugged into
the original slot, with interface transport reversed. -/
noncomputable def plug_iso_reverse
    (H : Hypernet ops d ((alphabet ops d).signature.input ((relabel C e l hi ho).edgeLabel e))
      ((alphabet ops d).signature.output ((relabel C e l hi ho).edgeLabel e))) :
    Net.Iso ((relabel C e l hi ho).plug e H)
      (C.plug e (H.reboundary (input_eq C e l hi ho).symm (output_eq C e l hi ho).symm)) := by
  have cancel {J K P Q : List Wire} (H : Hypernet ops d P Q) (a : J = P) (b : K = Q) :
      (H.reboundary a.symm b.symm).reboundary a b = H := by
    cases a; cases b; simp
  have a := plug_iso C e l hi ho
    (H.reboundary (input_eq C e l hi ho).symm (output_eq C e l hi ho).symm)
  rw [cancel] at a
  exact a.symm

/-- Replacing a slot by a focus-free label preserves global focus freedom. -/
theorem relabel_free (free : FocusFree C) (labelFree : LabelFocusFree ops d l) :
    FocusFree (relabel C e l hi ho) := by
  classical
  intro x
  by_cases eq : x = e
  · subst x; rw [selected_label]; exact labelFree
  · rw [other_label C e l hi ho x eq]; exact free x

/-- Closing the sole hole of a simple context with a hole-free label removes
all holes, including nested occurrences. -/
theorem close_holeFree
    (only : ∀ h (a : Occurrences C), occurrenceHole C a = some h → a.1 = e)
    (labelClosed : ∀ x : Fiber ops d l, fiberHole ops d l x = none) :
    HoleFree (relabel C e l hi ho) := by
  classical
  intro h present
  obtain ⟨⟨x,pos⟩,hp⟩ := (hasHole_iff_occurrences _ _).mp present
  by_cases eq : x = e
  · subst x
    have lab := selected_label C e l hi ho
    have same : fiberHole ops d l (lab ▸ pos) = some h := (fiberHole_transport lab pos).trans hp
    rw [labelClosed] at same
    cases same
  · have lab := other_label C e l hi ho x eq
    have old : occurrenceHole C ⟨x,lab ▸ pos⟩ = some h := (fiberHole_transport lab pos).trans hp
    exact eq (only h ⟨x,lab ▸ pos⟩ old)

end Relabel

/-- The hole retains the original slot's entire ordered interface. -/
def hole (name : Nat) : Hole :=
  ⟨name,(alphabet ops d).signature.input (C.edgeLabel e),(alphabet ops d).signature.output (C.edgeLabel e)⟩

/-- A concrete labelled simple context obtained by opening the selected slot. -/
noncomputable def openSlot (name : Nat) : Hypernet ops d I O :=
  relabel C e (primitiveLabel ops d (.hole (hole C e name)))
    (by cases d <;> rfl) (by cases d <;> rfl)

theorem open_label (name : Nat) : (openSlot C e name).edgeLabel e = primitiveLabel ops d (.hole (hole C e name)) :=
  selected_label ..

/-- Opening a slot in a focus-free graph gives a focus-free context. -/
theorem focusFree (name : Nat) (free : FocusFree C) : FocusFree (openSlot C e name) := by
  classical
  intro x
  by_cases eq : x = e
  · subst x
    rw [open_label]
    cases d <;> intro m bad <;> cases bad
  · rw [show (openSlot C e name).edgeLabel x = C.edgeLabel x from other_label C e _ _ _ x eq]
    exact free x

/-- If the original graph has no holes, every hole occurrence after opening
belongs to the selected shallow edge. -/
theorem occurrence_owner (name : Nat) (closed : HoleFree C)
    (a : Occurrences (openSlot C e name)) {h : Hole}
    (present : occurrenceHole (openSlot C e name) a = some h) : a.1 = e := by
  classical
  by_cases eq : a.1 = e
  · exact eq
  · have labels : (openSlot C e name).edgeLabel a.1 = C.edgeLabel a.1 := other_label C e _ _ _ a.1 eq
    apply False.elim
    apply closed h
    apply (hasHole_iff_occurrences C h).mpr
    refine ⟨⟨a.1,labels ▸ a.2⟩,?_⟩
    exact (fiberHole_transport labels a.2).trans present

/-- The opened edge has exactly one occurrence and no nested hole body. -/
theorem selected_fiber (name : Nat) : Subsingleton (Fiber ops d ((openSlot C e name).edgeLabel e)) := by
  rw [open_label]
  have unit : Subsingleton (Unit ⊕ Empty) := ⟨by
    intro a b
    rcases a with a | a
    · rcases b with b | b
      · cases a; cases b; rfl
      · exact nomatch b
    · exact nomatch a⟩
  cases d <;> exact unit

/-- The opened context has unique hole occurrences at all depths. -/
theorem unique (name : Nat) (closed : HoleFree C) : UniqueHoles ops d (openSlot C e name) := by
  apply (uniqueHoles_iff_occurrences _).mpr
  intro h a b ha hb
  have ea := occurrence_owner C e name closed a ha
  have eb := occurrence_owner C e name closed b hb
  rcases a with ⟨a,x⟩
  rcases b with ⟨b,y⟩
  dsimp at ea eb
  subst a
  subst b
  exact congrArg (Sigma.mk e) ((selected_fiber C e name).allEq x y)

/-- The one selected hole really occurs; simple-context witnesses are nonempty. -/
theorem present (name : Nat) : HasHole (openSlot C e name) (hole C e name) := by
  apply (hasHole_iff_occurrences _ _).mpr
  refine ⟨⟨e,.inl ()⟩,?_⟩
  change shallowHole ops d ((openSlot C e name).edgeLabel e) = _
  rw [open_label]
  cases d <;> rfl

/-- No second hole label occurs in the opened context. -/
theorem only_hole (name : Nat) (closed : HoleFree C) {h : Hole}
    (present : HasHole (openSlot C e name) h) : h = hole C e name := by
  obtain ⟨⟨a,x⟩,hx⟩ := (hasHole_iff_occurrences _ _).mp present
  have eq := occurrence_owner C e name closed ⟨a,x⟩ hx
  dsimp at eq
  subst a
  have eqx := (selected_fiber C e name).allEq x (.inl ())
  subst x
  change shallowHole ops d ((openSlot C e name).edgeLabel e) = some h at hx
  rw [open_label] at hx
  cases d <;> exact (Option.some.inj hx).symm

/-- A single shallow hole context has no additional focus or hole occurrences. -/
structure Simple (C : Hypernet ops d I O) (e : C.Edge) where
  hole : Hole
  label : C.edgeLabel e = primitiveLabel ops d (.hole hole)
  focusFree : FocusFree C
  only : ∀ h (a : Occurrences C), occurrenceHole C a = some h → a.1 = e

/-- Opening a slot supplies the paper's focus-free simple-context conditions. -/
def simple (name : Nat) (free : FocusFree C) (closed : HoleFree C) : Simple (openSlot C e name) e :=
  ⟨hole C e name,open_label C e name,focusFree C e name free,fun _ a h => occurrence_owner C e name closed a h⟩

/-- Every focus-free simple context can conversely be represented by a closed
slot host for any compatible focus-free, hole-free interaction label. -/
theorem close_simple (D : Simple C e) (l : (alphabet ops d).Symbol)
    (hi : (alphabet ops d).signature.input l = (alphabet ops d).signature.input (C.edgeLabel e))
    (ho : (alphabet ops d).signature.output l = (alphabet ops d).signature.output (C.edgeLabel e))
    (lf : LabelFocusFree ops d l) (lh : ∀ x : Fiber ops d l, fiberHole ops d l x = none) :
    FocusFree (relabel C e l hi ho) ∧ HoleFree (relabel C e l hi ho) :=
  ⟨relabel_free C e l hi ho D.focusFree lf,close_holeFree C e l hi ho D.only lh⟩

end Hypernets.Linear.SearchContexts

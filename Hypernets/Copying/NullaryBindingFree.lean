import Hypernets.Copying.NullaryTemplates
import Hypernets.Copying.BindingFillingWitness

/-! A nullary template cannot supply a sourced hole at any depth of a closed
recursive filling. Hence its actual common context is binding-free, even when
the observation class imposes no binding restriction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace NullaryOverlap
/-- A nonempty edge path into a hole supplies a source of its final edge. -/
theorem strictAncestor_source {d I O} {C : Hypernet d I O} {e f : C.Edge}
    (path : StrictAncestor C e f) : ∃ v, v ∈ C.source f := by
  obtain ⟨g,adj,path⟩ := path
  have source : ∃ v, v ∈ C.source g := by obtain ⟨v,_,mem⟩ := adj; exact ⟨v,mem⟩
  clear adj
  induction path with
  | refl => exact source
  | step adj _ ih =>
    obtain ⟨v,_,mem⟩ := adj
    exact ih ⟨v,mem⟩

/-- Every actual shallow hole of a closed nullary filling has no source.
Positive binding paths into such a hole are therefore impossible. -/
theorem shallow_bindingFree {T d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (closed : HoleFree (C.expand L)) : ShallowBindingFree C := by
  intro e f _ _ hole path
  obtain ⟨h,label⟩ := hole
  have nil := none ((cert f).relation_at_hole label closed)
  have length : (C.source f).length = 0 := by rw [C.source_length,nil]; rfl
  obtain ⟨v,mem⟩ := strictAncestor_source path
  have empty : C.source f = [] := List.length_eq_zero_iff.mp length
  rw [empty] at mem
  exact List.not_mem_nil mem

/-- Nullary template holes cannot be entered at any common-context position,
independently of token mode or wire type. -/
theorem not_entering {T d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (none : T.NoInputs)
    (closed : HoleFree (C.expand L)) (q : Search.Position C) :
    ¬ Search.Expansion.Entering C q := by
  rintro ⟨e,h,label,source⟩
  have nil := none ((cert e).relation_at_hole label closed)
  have length : (C.source e).length = 0 := by rw [C.source_length,nil]; rfl
  have empty : C.source e = [] := List.length_eq_zero_iff.mp length
  rw [empty] at source
  exact List.not_mem_nil source
end NullaryOverlap

/-- Nullarity is checked again inside every original box, using the actual
closed left filling. Unfilled holes cannot remain hidden in a retained corolla. -/
theorem DeepFilling.nullary_bindingFree {T d I O} {C L R : Hypernet d I O}
    (pair : DeepFilling T C L R) (none : T.NoInputs)
    (free : FocusFree C) (closed : HoleFree L) : BindingFree C := by
  induction d generalizing I O with
  | zero =>
    cases pair with
    | expand C L R cert => exact ⟨free,NullaryOverlap.shallow_bindingFree C cert none closed⟩
  | succ d ih =>
    cases pair with
    | expand C L R cert =>
      refine ⟨free,NullaryOverlap.shallow_bindingFree C cert none closed,?_⟩
      intro e
      cases cert e with
      | retained l r =>
        have h := closed ⟨e,l.edge⟩
        change LabelAll (fun p => ∀ h, p ≠ .hole h) (d+1) ((L e).edgeLabel l.edge) at h
        rw [l.edge_label] at h
        cases label : C.edgeLabel e with
        | inl p => trivial
        | inr b =>
          rw [label] at h
          exact BindingFree.paths_of_holeFree d b.body h
      | filled h label rel => rw [label]; trivial
      | boxed b label inner l r =>
        rw [label]
        have bf : FocusFree b.body := by have h := free e; rw [label] at h; exact h
        have hc := closed ⟨e,l.edge⟩
        change LabelAll (fun p => ∀ h, p ≠ .hole h) (d+1) ((L e).edgeLabel l.edge) at hc
        rw [l.edge_label] at hc
        exact (ih inner bf hc).2

/-- An actual witness inherits the restriction from its certified left endpoint;
this is a conclusion and does not restrict the surrounding observation class. -/
theorem FillingWitness.nullary_bindingFree {T d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (none : T.NoInputs) (closed : HoleFree G) : BindingFree w.context :=
  w.paired.nullary_bindingFree none w.free ((allLabels_iso_iff _ w.leftIso).mpr closed)
end Hypernets.Copying

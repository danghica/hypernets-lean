import Hypernets.Copying.BindingClosure

/-! Binding-freedom does not depend on recursive carrier names. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph

theorem bindingLabel_equiv (d : Nat) {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    BindingLabel d a ↔ BindingLabel d b := by
  cases d with
  | zero => cases h; rfl
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => rfl

theorem holeLabel_equiv (d : Nat) {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    HoleLabel d a ↔ HoleLabel d b := by
  cases d with
  | zero => cases h; rfl
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => simp [HoleLabel,primitiveLabel]

theorem shallow_iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (free : ShallowBindingFree H) : ShallowBindingFree G := by
  apply shallow_of_map f.edges.toFun (fun h => (f.adjacent_iff _ _).mpr h)
    (fun e h => (bindingLabel_equiv d (f.edge_label e)).mp h) ?_
    (fun e h => (holeLabel_equiv d (f.edge_label e)).mp h) free
  intro e src
  obtain ⟨v,hv⟩ := src
  exact ⟨Port.map f.vertices.toFun v,by rw [← f.source]; exact List.mem_map_of_mem hv⟩

theorem paths_iso (d : Nat) {I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (free : BindingPaths d H) : BindingPaths d G := by
  induction d generalizing I O with
  | zero => exact shallow_iso f free
  | succ d ih =>
    refine ⟨shallow_iso f free.1,?_⟩
    intro e
    have rel := f.edge_label e
    have inner := free.2 (f.edges.toFun e)
    cases a : G.edgeLabel e with
    | inl p => trivial
    | inr b =>
      cases z : H.edgeLabel (f.edges.toFun e) with
      | inl p => simp [a,z,LabelEquiv] at rel
      | inr c =>
        simp only [a,z,LabelEquiv] at rel
        rw [z] at inner
        cases rel with
        | bodies related =>
          obtain ⟨g⟩ := related
          exact ih g inner

theorem iso_iff {d I O} {G H : Hypernet d I O} (f : DeepIso G H) :
    BindingFree G ↔ BindingFree H := by
  constructor
  · intro free
    exact ⟨(allLabels_iso_iff _ f).mp free.1,paths_iso d f.symm free.2⟩
  · intro free
    exact ⟨(allLabels_iso_iff _ f).mpr free.1,paths_iso d f free.2⟩
end Hypernets.Copying.BindingFree

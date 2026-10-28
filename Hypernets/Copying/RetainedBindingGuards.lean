import Hypernets.Copying.BindingStoreRewrite

/-! Retention preserves whether an outer edge is binding even when its box
body is recursively changed. Primitive-footprint restrictions are unnecessary
for transporting a sourced binding ancestry to the original skeleton. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Search.Expansion.Retained
theorem bindingLabel_iff {d I O} {C : Hypernet d I O} {L e} (r : Retained C L e) :
    BindingLabel d ((L e).edgeLabel r.edge) ↔ BindingLabel d (C.edgeLabel e) := by
  cases d with
  | zero =>
    have eq := (r.primitive ((L e).edgeLabel r.edge).down).mp rfl
    exact iff_of_eq (congrArg (BindingLabel 0) eq).symm
  | succ d =>
    cases left : (L e).edgeLabel r.edge with
    | inl p =>
      have eq := (r.primitive p).mp left
      rw [eq]
      rfl
    | inr b =>
      cases right : C.edgeLabel e with
      | inl p =>
        have eq := (r.primitive p).mpr right
        rw [left] at eq
        cases eq
      | inr a => rfl
end Search.Expansion.Retained

namespace RetainedFootprint
theorem skeleton_bindingGuarded_full {d I O J K} (C : Hypernet d I O) {L R}
    {A : Hypernet d J K} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding) (guard : BindingGuardedOutputs A) :
    BindingGuardedOutputs (skeleton C f cert avoid) := by
  intro i
  obtain ⟨e,g,binding,source,path,target⟩ := guard i
  refine ⟨e,g,?_,source,Ancestor.map (G := A) (H := skeleton C f cert avoid)
    (fun e => e) (fun adj => adj) path,target⟩
  exact (left C f.matchEmbedding cert avoid e).bindingLabel_iff.mp
    ((BindingFree.bindingLabel_equiv d (sourceLabel C f cert avoid e)).mp binding)
end RetainedFootprint
end Hypernets.Copying

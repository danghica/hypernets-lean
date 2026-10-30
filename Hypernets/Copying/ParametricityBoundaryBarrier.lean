import Hypernets.Copying.ParametricityTemplate
import Hypernets.Copying.NoOutputOverlap

/-! Exact entry and no-exit boundaries of the private Figure 20 families,
in both directions and in arbitrary original recursive filling contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

/-- Every component input is sourced by a lambda value at the surface. -/
def PreTemplate.LambdaEntries (T : PreTemplate) : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → Parametricity.LambdaInputs G

namespace LambdaEntryOverlap
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
include cert heads

/-- A non-lambda edge sourcing a host vertex cannot belong to a fresh
shallow family. This retains the exact original incidence and label. -/
theorem source_retained {v : C.Vertex} {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (different : (C.expand L).edgeLabel e ≠ primitiveLabel d (.operation .lam)) :
    Nonempty (Retained C L e.1) := by
  rcases (cert e.1).origin with copies | ⟨h,label,rel⟩
  · exact copies.1
  · obtain ⟨i,mem⟩ := source_input C source
    obtain ⟨a,head⟩ := heads rel i
    have same := (L e.1).source_unique mem head.2
    apply False.elim (different _)
    change (L e.1).edgeLabel e.2 = _
    exact same ▸ head.1

/-- Any sourced edge of a shallow family is its boundary lambda edge.
The hypothesis records the actual original hole, not a chosen presentation. -/
theorem shallow_source_label (closed : HoleFree (C.expand L))
    {v : C.Vertex} {e : (C.expand L).Edge} {h : Hole}
    (hole : C.edgeLabel e.1 = primitiveLabel d (.hole h))
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e) :
    (C.expand L).edgeLabel e = primitiveLabel d (.operation .lam) := by
  have rel := (cert e.1).relation_at_hole hole closed
  obtain ⟨i,mem⟩ := source_input C source
  obtain ⟨a,head⟩ := heads rel i
  have same := (L e.1).source_unique mem head.2
  change (L e.1).edgeLabel e.2 = _
  exact same ▸ head.1

/-- Hole freedom excludes retained unfilled holes at non-lambda sources. -/
theorem source_not_hole (closed : HoleFree (C.expand L))
    {v : C.Vertex} {e : (C.expand L).Edge}
    (source : Net.Expansion.host C L v ∈ (C.expand L).source e)
    (different : (C.expand L).edgeLabel e ≠ primitiveLabel d (.operation .lam)) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h hole
  exact different (shallow_source_label C cert heads closed hole source)

/-- A whole mapped operational ancestry with no lambda surface remains in
the original context, while arbitrary deep box bodies stay unrestricted. -/
theorem ancestor_retained {J K} {A : Hypernet d J K}
    (f : MatchEmbedding A (C.expand L))
    (different : ∀ e, (C.expand L).edgeLabel (f.edges e) ≠ primitiveLabel d (.operation .lam))
    {a b : A.Edge} (path : Ancestor A a b)
    (initial : Nonempty (Retained C L (f.edges a).1)) :
    Nonempty (Retained C L (f.edges b).1) ∧
      Ancestor C (f.edges a).1 (f.edges b).1 := by
  induction path with
  | refl => exact ⟨initial,.refl _⟩
  | @step a b c adj path ih =>
    obtain ⟨copy⟩ := initial
    have mapped := f.adjacent adj
    have original := BindingOverlap.adjacent_owner C copy mapped
    obtain ⟨w,target,source⟩ := mapped
    obtain ⟨u,eq⟩ := copy.target_origin target
    have next := source_retained C cert heads (eq ▸ source) (different b)
    obtain ⟨retained,ancestry⟩ := ih next
    exact ⟨retained,.step original ancestry⟩

end LambdaEntryOverlap

namespace Parametricity

/-- Both independent representations preserve the actual lambda entry. -/
theorem Pair.input_heads {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) : LambdaInputs G ∧ LambdaInputs H := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | families d C =>
      constructor
      · intro i
        obtain ⟨e,head⟩ := left_lambdaInputs d C i
        exact ⟨_,(MatchEmbedding.ofDeepIso f.symm).head head⟩
      · intro i
        obtain ⟨e,head⟩ := right_lambdaInputs d _ _ i
        exact ⟨_,(MatchEmbedding.ofDeepIso g).head head⟩

theorem template_lambdaEntries : template.LambdaEntries := fun pair => pair.input_heads.1
theorem converse_lambdaEntries : template.converse.LambdaEntries := fun pair => pair.input_heads.2

/-- The complete private cell and all sharing resources have no escaping
wire, regardless of family multiplicities or recursive graph carriers. -/
theorem template_noOutputs : template.NoOutputs := fun pair => pair.noOutputs
theorem converse_noOutputs : template.converse.NoOutputs := template_noOutputs.converse

end Parametricity
end Hypernets.Copying

import Hypernets.Copying.ConverseStoreOverlap
import Hypernets.Copying.RetainedBindingGuards

/-! A binding argument and all of its descendants in an actual right match
remain in the original binding-free context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Search.Expansion MatchEmbedding

/-- Rooted argument evaluation retains the first binding edge; the original
binding-free path condition then retains every edge downstream of it. -/
theorem argument_binding_descendant_not_hole {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {input v}
    (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    {head a b : (C.expand R).Edge} {o}
    (selected : HeadAt (C.expand R) (Net.Expansion.host C R v) head (.operation o))
    (active : o.kind = .active) (argument : (C.expand R).Adjacent head a)
    (binding : BindingLabel d ((C.expand R).edgeLabel a))
    (path : Ancestor (C.expand R) a b) :
    ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
  have avoid := adjacent_source_not_hole C cert away rooted selected active argument
  obtain ⟨_,copy⟩ := (cert a.1).retained_of_not_hole avoid
  have originalBinding : BindingLabel d (C.edgeLabel a.1) := by
    apply copy.bindingLabel_iff.mp
    change BindingLabel d ((R a.1).edgeLabel a.2) at binding
    simpa only [copy.only a.2] using binding
  obtain ⟨⟨headCopy⟩,_⟩ := BindingOverlap.head_retained C (fun e => (cert e).converse) away selected
  obtain ⟨u,_,source⟩ := BindingOverlap.adjacent_owner C headCopy argument
  obtain ⟨_,ancestry⟩ := BindingOverlap.ancestor_retained C (fun e => (cert e).converse)
    free.shallow a.1 originalBinding ⟨u,source⟩ path ⟨copy⟩ (.refl _)
  intro h hole
  have different : a.1 ≠ b.1 := by intro eq; exact avoid h (eq ▸ hole)
  exact free.shallow _ _ originalBinding ⟨u,source⟩ ⟨h,hole⟩ (ancestry.positive_of_ne different)

end Hypernets.Copying.OperationalTemplates.ConverseOverlap

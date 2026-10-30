import Hypernets.Copying.CopyingTemplateLaws
import Hypernets.Copying.TemplateConsumption

/-! The original copying entry transitions, with all tree inputs retained.
The distinguished first input consumes the template in exactly two machine
transitions. Other inputs request copying too, but their residual comparison
is a separate associativity/commutativity obligation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined

/-- Every input of the original tree requests copying in one search step;
this includes the inputs that are not distinguished by the displayed rule. -/
theorem requests_copy {d n k h} (tree : ContractionTree .term (n+1))
    (H : Hypernet d [.term] (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length) :
    Search.Step (CopyRule.before tree H) (.search,.input i) (.rewrite,.input i) := by
  obtain ⟨e,label,source⟩ := CopyRule.before_active_head tree H i
  exact .search e (.contraction .term) _ _ label source rfl

/-- Independent recursive graph representations preserve the search request
at every original external input coordinate. -/
theorem Pair.search_request {d I O} {G H : Hypernet d I O} (pair : Pair G H)
    (i : Fin I.length) : Search.Step G (.search,.input i) (.rewrite,.input i) := by
  cases pair with
  | witness f p g =>
    cases p with
    | copy tree A copyable free =>
      exact (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step (requests_copy tree A i)

/-- The distinguished first input executes exactly the original local copy
rule, returning to search at that same input on the actual displayed reduct. -/
theorem Pair.selected_entry_prefix {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    ∃ i : Fin I.length, i.val = 0 ∧
      Trace (Search.Step G) (.search,.input i) (.rewrite,.input i) 1 ∧
      Rewrite G (.input i) H (.input i) := by
  cases pair with
  | witness f p g =>
    cases p with
    | copy tree A copyable free =>
      refine ⟨⟨0,by simp⟩,rfl,?_,.rename f.symm g (.local (.copy tree A copyable))⟩
      exact .step ((Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step
        (requests_copy tree A ⟨0,by simp⟩)) (.refl _)

/-- At the first input the original entered hole is consumed into the common
context, with every other shallow or deep replacement retained. The left
endpoint takes two transitions and the right endpoint takes none. -/
theorem consume_selected {Allowed} (S : Specimen template Allowed) (e : S.context.Edge)
    (pair : Pair (S.left e) (S.right e))
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (first : i.val = 0) (token : S.token = (.search,S.context.sourcePort e i))
    (allowed : Allowed S.depth (S.context.plug e (S.right e))) :
    ∃ D : Specimen template Allowed,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps 2 (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState S.rightState := by
  obtain ⟨j,first',trace,rewrite⟩ := pair.selected_entry_prefix
  have index : j = i := Fin.ext (first'.trans first.symm)
  subst j
  exact TemplateConsumption.consume S e i token 1 trace rewrite pair.focusFree.2 allowed

/-- Unrestricted contexts discharge the selected-input consumption without
an additional context admissibility premise. -/
theorem consume_selected_allContexts (S : Specimen template Specimens.allContexts)
    (e : S.context.Edge) (pair : Pair (S.left e) (S.right e))
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (first : i.val = 0) (token : S.token = (.search,S.context.sourcePort e i)) :
    ∃ D : Specimen template Specimens.allContexts,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps 2 (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState S.rightState :=
  consume_selected S e pair i first token trivial

/-- The same first-input residual is binding-free by the proved sourced-hole
plugging law and the actual closed right component. -/
theorem consume_selected_bindingFree (S : Specimen template Specimens.bindingFreeContexts)
    (e : S.context.Edge) (hole : HoleLabel S.depth (S.context.edgeLabel e))
    (pair : Pair (S.left e) (S.right e))
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (first : i.val = 0) (token : S.token = (.search,S.context.sourcePort e i)) :
    ∃ D : Specimen template Specimens.bindingFreeContexts,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps 2 (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState S.rightState := by
  apply consume_selected S e pair i first token
  exact BindingFree.plugAt (.shallow S.context e) (S.right e)
    ⟨hole,⟨S.context.sourcePort e i,S.context.sourcePort_mem e i⟩⟩ S.allowed
    (BindingFree.of_holeFree (S.right e) pair.focusFree.2 (fun x => S.right_closed ⟨e,x⟩))

end Hypernets.Copying.CopyingTemplate

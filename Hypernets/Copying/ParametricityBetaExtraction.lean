import Hypernets.Copying.LambdaEntryAssignmentOverlap
import Hypernets.Copying.ParametricityBareApplyContext
import Hypernets.Copying.CopyingTemplateFirstShallow

/-! An actual opening match determines the original application edge and
the exact ordered input of its selected family component. The argument is
never matched or required to lie outside a shallow family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    {k h} {B : Hypernet d [.term] (environmentInterface (k+1) h)} {v : C.Vertex}
    (a : Application.Match (C.expand L) (Net.Expansion.host C L v) B)
include cert heads

/-- The retained actual application and the selected component input form
an original common-context footprint; only their genuine incidence is used. -/
theorem beta_entry :
    ∃ f : Occurrence (primitiveNet (d+1) (.operation .app)) C,
      f.ports (.input (0 : Fin 1)) = v ∧
      (∀ x, C.edgeLabel (f.edges x) = primitiveLabel (d+1) (.operation .app)) ∧
      ∃ i : Fin ((alphabet (d+1)).signature.input (C.edgeLabel a.lam.1)).length,
        f.ports (.output (0 : Fin 2)) = C.sourcePort a.lam.1 i := by
  obtain ⟨copy⟩ := source_retained C cert heads a.head_at.2 (by
    rw [a.head_at.1]; intro eq; cases primitiveLabel_injective (d+1) eq)
  have label := retained_primitive C copy a.head_at.1
  let f := Occurrence.primitive C a.app.1 label
  have source : [f.ports (.input (0 : Fin 1))] = C.source a.app.1 := f.source (0 : Fin 1)
  have originalSource : C.source a.app.1 = [v] :=
    Search.operation_source label (source_owner C L a.head_at.2)
  have point : f.ports (.input (0 : Fin 1)) = v := (List.cons.inj (source.trans originalSource)).1
  have target : [f.ports (.output (0 : Fin 2)),f.ports (.output (1 : Fin 2))] = C.target a.app.1 :=
    f.target (0 : Fin 1)
  have expanded := (congrArg (fun xs => xs.map (Net.Expansion.host C L)) target).trans
    ((retained_target C copy).symm.trans a.app_target)
  have functionPoint : Net.Expansion.host C L (f.ports (.output (0 : Fin 2))) = .internal a.functionWire :=
    (List.cons.inj expanded).1
  have lambdaSource : Net.Expansion.host C L (f.ports (.output (0 : Fin 2))) ∈ (C.expand L).source a.lam := by
    rw [functionPoint,a.lambda_source]
    exact List.mem_singleton_self _
  obtain ⟨i,_,attached⟩ := CopyingTemplate.Remote.source_input_exact C lambdaSource
  exact ⟨f,point,(fun x => f.matchEmbedding.primitive x (.operation .app) rfl),i,attached.symm⟩

end Hypernets.Copying.LambdaEntryOverlap

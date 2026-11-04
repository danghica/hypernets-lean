import Hypernets.Copying.ParametricityBareApplyContext
import Hypernets.Copying.CopyingInputExpansion
import Hypernets.Copying.CopyingInputIsomorphism
import Hypernets.Copying.CopyingRemoteSource

/-! The computed original application/hole cut expands to exactly the bare
application of its complete selected filling. No argument graph is cut out. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt.Context
open Graph Opening
variable {d n} (name : Nat) (j : Fin (n+1))
    (U : Hypernet d (List.replicate (n+1) .term) [])

def filledFamily (x : (net (hole (d := d) (n := n) name) j).Edge) :
    Hypernet d ((alphabet d).signature.input ((net (hole (d := d) (n := n) name) j).edgeLabel x))
      ((alphabet d).signature.output ((net (hole (d := d) (n := n) name) j).edgeLabel x)) := by
  cases d <;> rcases x with ⟨side,x⟩ <;> cases side
  all_goals first | exact primitiveNet _ (.operation .app) | exact U

/-- Reassociate actual simultaneous expansion, collapse only the unchanged
application corolla, and fill the whole original selected hole. -/
noncomputable def filledIso :
    DeepIso ((net (hole (d := d) (n := n) name) j).expand (filledFamily name j U)) (net U j) := by
  let Z := hole (d := d) (n := n) name
  cases d
  all_goals
    have assoc := DeepIso.ofIso (Net.ExpansionAssoc.iso (BareApplyFirst.pattern n _)
      (BareApplyFirst.filling (selected Z j)) (fun e x => filledFamily name j U ⟨e,x⟩))
    have same : Net.ExpansionAssoc.flat (BareApplyFirst.pattern n _)
        (BareApplyFirst.filling (selected Z j)) (fun e x => filledFamily name j U ⟨e,x⟩) =
          filledFamily name j U := by funext e;cases e;rfl
    rw [same] at assoc
    apply assoc.trans
    apply Net.ExpansionIso.iso
    intro e
    cases e
    · apply DeepIso.ofIso
      apply FillingCollapse.identity
      intro x
      exact LabelCopy.corolla _
    · exact (CopyingInputPermutation.expansionIso Z (order j).symm
        (CopyingTemplate.RemoteContext.holeFamily name U)).trans
          (CopyingInputPermutation.congr (CopyingTemplate.RemoteContext.holeIso name U) (order j).symm)

variable {I O} (C : Hypernet d I O)
    (a : Occurrence (primitiveNet d (.operation .app)) C) (e : C.Edge)
    (label : C.edgeLabel e = primitiveLabel d (.hole ⟨name,List.replicate (n+1) .term,[]⟩))
    (link : a.ports (.output (0 : Fin 2)) = C.sourcePort e
      ⟨j.val,by rw [label,primitive_input];simp [primitiveSignature]⟩)
    (F : (x : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel x))
      ((alphabet d).signature.output (C.edgeLabel x)))
    (copies : ∀ x, LabelCopy (F (a.edges x)) (primitiveLabel d (.operation .app)))
    (selected : DeepIso ((F e).reboundary
      (by rw [label,primitive_input];rfl) (by rw [label,primitive_output];rfl)) U)

/-- The actual computed original common-context cut has exactly the stated
bare source, retaining the entire callback graph outside the selected cut. -/
noncomputable def sourceIso :
    DeepIso ((CommonContextCut.skeleton C (occurrence C a e name label j link)).expand
      (CommonContextCut.localFamily C (occurrence C a e name label j link) F)) (net U j) := by
  apply (CommonContextCut.localIso C (occurrence C a e name label j link) F
    (filledFamily name j U) ?_).trans (filledIso name j U)
  intro x
  cases d
  all_goals
    rcases x with ⟨side,x⟩
    cases side
    · exact ((copies x).reboundary _ _).iso (LabelCopy.corolla _) (labelEquiv_refl _ _)
    · exact selected

end Hypernets.Copying.Parametricity.BareApplyAt.Context

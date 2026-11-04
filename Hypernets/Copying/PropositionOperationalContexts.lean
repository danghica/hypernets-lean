import Hypernets.Copying.PropositionAllocationGeometry
import Hypernets.Copying.NestedContextFilling

/-! The actual binding-free contexts used by the allocation and micro-beta
links. These supply their own sole-hole and path certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Proposition12_2
open Graph

noncomputable def applicationContext {d} (G : Hypernet d [.term] [])
    (free : FocusFree G) (holes : HoleFree G) : GraphContext d 0 0 d 0 0 where
  graph := Serial.net (primitiveNet d (.operation .app))
    (Net.Tensor.net G (ContextTranslation.hole d 0 0 0).2)
  site := Serial.rightSite _ (ParallelPair.rightSite (Net.Tensor.boundary [Wire.term] [] [Wire.term] [])
    G (ContextTranslation.holeSite d 0 0 0))
  sole := Serial.rightSite_sole _
    (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq)) _
      (ParallelPair.rightSite_sole _ G holes _ (ContextTranslation.holeSite_sole d 0 0 0))
  bindingFree := by
    apply BindingFree.operation_prefix
    apply BindingFree.parallel
    intro b; cases b
    · exact BindingFree.of_holeFree G free holes
    · exact Examples.hole_bindingFree d _

noncomputable def applicationContext_fill {d} (G : Hypernet d [.term] [])
    (free : FocusFree G) (holes : HoleFree G) (A : OpenProgram d 0 0) :
    DeepIso ((applicationContext G free holes).fill A).graph
      (Serial.net (primitiveNet d (.operation .app)) (Net.Tensor.net G A.graph)) :=
  (Serial.plugAt_right _ _ _).trans
    (Serial.congr (DeepIso.refl _)
      ((ParallelPair.plugAt_right (Net.Tensor.boundary [Wire.term] [] [Wire.term] []) G _ _).trans
        (BoxPermutation.tensor_congr (DeepIso.refl _) (ContextTranslation.hole_filling 0 A.graph))))

noncomputable def storeContext {d} (R : Hypernet d [.atom] [])
    (free : FocusFree R) (holes : HoleFree R) : GraphContext d 0 1 d 0 0 where
  graph := Serial.net (ContextTranslation.hole d 0 0 1).2 R
  site := Serial.leftSite R (ContextTranslation.holeSite d 0 0 1)
  sole := Serial.leftSite_sole R holes _ (ContextTranslation.holeSite_sole d 0 0 1)
  bindingFree := BindingFree.serial_suffix _ _ (Examples.hole_bindingFree d _) free holes

noncomputable def storeContext_fill {d} (R : Hypernet d [.atom] [])
    (free : FocusFree R) (holes : HoleFree R) (A : OpenProgram d 0 1) :
    DeepIso ((storeContext R free holes).fill A).graph (Serial.net A.graph R) :=
  (Serial.plugAt_left R _ _).trans (Serial.congr (ContextTranslation.hole_filling 0 A.graph) (DeepIso.refl _))

/-- Use a proved contextual comparison in an actual certified context, then
identify the literal endpoints by their proved whole-graph isomorphisms. -/
theorem context_equiv {r v a d k h} (C : GraphContext r v a d k h)
    (G H : OpenProgram r v a) (L R : OpenProgram d k h)
    (rel : Combined.execution.Equiv CostOrder.any G H)
    (left : DeepIso (C.fill G).graph L.graph) (right : DeepIso (C.fill H).graph R.graph) :
    Combined.execution.Equiv CostOrder.any L R :=
  Combined.execution.equiv_trans
    (Combined.execution.equiv_symm (Combined.execution.equiv_iso Combined.execution_respectsIso _ _ left))
      (Combined.execution.equiv_trans (Combined.equiv_context C rel)
        (Combined.execution.equiv_iso Combined.execution_respectsIso _ _ right))
end Hypernets.Copying.Proposition12_2

import Hypernets.Copying.SharingSameContext
import Hypernets.Copying.CommonContextExpansion
import Hypernets.Copying.CommonContextPrimitive
import Hypernets.Copying.CommonContextBoundary
import Hypernets.Copying.CopyTransport

/-! Exact normalization of the selected original same-equality context into the
unchanged local same-store equality rule, retaining its complete sharing tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Same.Context
open Graph Opening

/-- Comparing two entries of a literal atom tree in the common frame is the original rule graph. -/
def graphIso {d h} (A : ContractionTree .atom (h+2)) :
    DeepIso (graph (A.atDepth d)) (before A d) := by
  have eq : family (A.atDepth d) = FillingWitness.liftedFamily (beforeFrame h) (beforeFill A) d := by
    cases d <;> funext e <;> cases e <;> simp only [family,Net.reboundary_refl] <;> rfl
  rw [graph,eq]
  exact FillingWitness.primitiveExpansionIso (beforeFrame h) (beforeFill A) d

variable {T : PreTemplate} {d h I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    {W : Hypernet d (List.replicate (h+2) .atom) [.atom]}
    (f : Occurrence W C) (compare first second store : C.Edge)
    (compareLabel : C.edgeLabel compare = primitiveLabel d (.operation (.binary .atomEq)))
    (firstLabel : C.edgeLabel first = primitiveLabel d .instanceEdge)
    (secondLabel : C.edgeLabel second = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (t u u' v v' z o : C.Vertex)
    (compareSource : C.source compare = [t]) (compareTarget : C.target compare = [u,u'])
    (firstSource : C.source first = [u]) (firstTarget : C.target first = [v])
    (secondSource : C.source second = [u']) (secondTarget : C.target second = [v'])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v)
    (treeSecond : f.ports (.input ⟨1,by simp⟩) = v') (treeOutput : f.ports (.output 0) = z)
    (distinct : first ≠ second)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)))
    (A : ContractionTree .atom (h+2))
    (treeIso : DeepIso ((CommonContextCut.skeleton C f).expand
      (CommonContextCut.localFamily C f L)) (A.atDepth d))

/-- Original fillers of every selected component normalize separately: the
comparison, both instances and store are retained, and the actual sharing tree is kept. -/
noncomputable def componentIso (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    DeepIso
      ((CommonContextCut.skeleton C (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e)).expand
        (CommonContextCut.localFamily C (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e) L))
      (family (A.atDepth d) e) := by
  cases e with
  | tree =>
    exact (CommonContextCut.reboundarySourceIso C f L _ _).trans
      (CopyRule.reboundaryIso treeIso _ _)
  | compare =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel .compare)
      (fun _ => ⟨.operation (.binary .atomEq),rfl,by intro h eq; cases eq⟩)
  | left =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel .left)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | right =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel .right)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | store =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel .store)
      (fun _ => ⟨.store,rfl,by intro h eq; cases eq⟩)

/-- Regrouping the actual selected cut gives exactly the original complete
local comparison source, including every inactive sharing branch. -/
noncomputable def sourceIso : DeepIso
    ((CommonContextCut.skeleton C (occurrence C f compare first second store compareLabel firstLabel secondLabel storeLabel
      t u u' v v' z o compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput distinct sharing)).expand
      (CommonContextCut.localFamily C (occurrence C f compare first second store compareLabel firstLabel secondLabel storeLabel
        t u u' v v' z o compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput distinct sharing) L))
    (before A d) := by
  let last : DeepIso
      ((FillingWitness.liftedFrame (beforeFrame h) d).expand (fun e =>
        (CommonContextCut.skeleton C (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e)).expand
          (CommonContextCut.localFamily C (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e) L)))
      (graph (A.atDepth d)) :=
    Net.ExpansionIso.iso (FillingWitness.liftedFrame (beforeFrame h) d)
      (componentIso C cert f compare first second store compareLabel firstLabel secondLabel storeLabel A treeIso)
  exact (CommonContextCut.expansionIso C (FillingWitness.liftedFrame (beforeFrame h) d) (family W)
    (components C f compare first second store compareLabel firstLabel secondLabel storeLabel) (host C f t u u' v v' z o)
    (components_input C f compare first second store compareLabel firstLabel secondLabel storeLabel t u u' v v' z o
      compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput)
    (components_output C f compare first second store compareLabel firstLabel secondLabel storeLabel t u u' v v' z o
      compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput)
    (components_disjoint C f compare first second store compareLabel firstLabel secondLabel storeLabel distinct sharing) L).trans
      (last.trans (graphIso A))

end Hypernets.Copying.AtomEquality.Same.Context

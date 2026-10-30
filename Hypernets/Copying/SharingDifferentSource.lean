import Hypernets.Copying.SharingDifferentContext
import Hypernets.Copying.CommonContextExpansion
import Hypernets.Copying.CommonContextPrimitive
import Hypernets.Copying.CommonContextBoundary
import Hypernets.Copying.CopyTransport

/-! Exact normalization of the selected original different-equality context into the
unchanged local different-store equality rule, retaining both complete sharing trees. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Different.Context
open Graph Opening

/-- Comparing entries of two literal atom trees in the common frame is the original rule graph. -/
def graphIso {d n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1)) :
    DeepIso (graph (A.atDepth d) (B.atDepth d)) (before A B d) := by
  have eq : family (A.atDepth d) (B.atDepth d) = FillingWitness.liftedFamily (beforeFrame n m) (beforeFill A B) d := by
    cases d <;> funext e <;> cases e <;> simp only [family,Net.reboundary_refl] <;> rfl
  rw [graph,eq]
  exact FillingWitness.primitiveExpansionIso (beforeFrame n m) (beforeFill A B) d

variable {T : PreTemplate} {d n m I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    {W : Hypernet d (List.replicate (n+1) .atom) [.atom]}
    {V : Hypernet d (List.replicate (m+1) .atom) [.atom]}
    (f : Occurrence W C) (g : Occurrence V C) (compare first second store storeRight : C.Edge)
    (compareLabel : C.edgeLabel compare = primitiveLabel d (.operation (.binary .atomEq)))
    (firstLabel : C.edgeLabel first = primitiveLabel d .instanceEdge)
    (secondLabel : C.edgeLabel second = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (storeRightLabel : C.edgeLabel storeRight = primitiveLabel d .store)
    (t u u' v v' z z' o o' : C.Vertex)
    (compareSource : C.source compare = [t]) (compareTarget : C.target compare = [u,u'])
    (firstSource : C.source first = [u]) (firstTarget : C.target first = [v])
    (secondSource : C.source second = [u']) (secondTarget : C.target second = [v'])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (storeRightSource : C.source storeRight = [z']) (storeRightTarget : C.target storeRight = [o'])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v)
    (treeSecond : g.ports (.input ⟨0,by simp⟩) = v') (treeOutput : f.ports (.output 0) = z)
    (treeRightOutput : g.ports (.output 0) = z')
    (distinct : first ≠ second) (stores : store ≠ storeRight)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)))
    (sharingRight : ∀ e, SharingLabel d .atom (C.edgeLabel (g.edges e)))
    (apart : ∀ e j, f.edges e ≠ g.edges j)
    (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1))
    (treeIso : DeepIso ((CommonContextCut.skeleton C f).expand
      (CommonContextCut.localFamily C f L)) (A.atDepth d))
    (treeRightIso : DeepIso ((CommonContextCut.skeleton C g).expand
      (CommonContextCut.localFamily C g L)) (B.atDepth d))

/-- Original fillers of every selected component normalize separately: the
comparison, both instances and both stores are retained, and both actual sharing trees are kept. -/
noncomputable def componentIso (e : (FillingWitness.liftedFrame (beforeFrame n m) d).Edge) :
    DeepIso
      ((CommonContextCut.skeleton C (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e)).expand
        (CommonContextCut.localFamily C (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e) L))
      (family (A.atDepth d) (B.atDepth d) e) := by
  cases e with
  | tree =>
    exact (CommonContextCut.reboundarySourceIso C f L _ _).trans
      (CopyRule.reboundaryIso treeIso _ _)
  | treeRight =>
    exact (CommonContextCut.reboundarySourceIso C g L _ _).trans
      (CopyRule.reboundaryIso treeRightIso _ _)
  | storeRight =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel .storeRight)
      (fun _ => ⟨.store,rfl,by intro h eq; cases eq⟩)
  | compare =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel .compare)
      (fun _ => ⟨.operation (.binary .atomEq),rfl,by intro h eq; cases eq⟩)
  | left =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel .left)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | right =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel .right)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | store =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel .store)
      (fun _ => ⟨.store,rfl,by intro h eq; cases eq⟩)

/-- Regrouping the actual selected cut gives exactly the original complete
local comparison source, including every inactive sharing branch. -/
noncomputable def sourceIso : DeepIso
    ((CommonContextCut.skeleton C (occurrence C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel
      t u u' v v' z z' o o' compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput distinct stores sharing sharingRight apart)).expand
      (CommonContextCut.localFamily C (occurrence C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel
        t u u' v v' z z' o o' compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput distinct stores sharing sharingRight apart) L))
    (before A B d) := by
  let last : DeepIso
      ((FillingWitness.liftedFrame (beforeFrame n m) d).expand (fun e =>
        (CommonContextCut.skeleton C (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e)).expand
          (CommonContextCut.localFamily C (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e) L)))
      (graph (A.atDepth d) (B.atDepth d)) :=
    Net.ExpansionIso.iso (FillingWitness.liftedFrame (beforeFrame n m) d)
      (componentIso C cert f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel A B treeIso treeRightIso)
  exact (CommonContextCut.expansionIso C (FillingWitness.liftedFrame (beforeFrame n m) d) (family W V)
    (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel) (host C f g t u u' v v' z z' o o')
    (components_input C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel t u u' v v' z z' o o'
      compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput)
    (components_output C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel t u u' v v' z z' o o'
      compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput)
    (components_disjoint C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel distinct stores sharing sharingRight apart) L).trans
      (last.trans (graphIso A B))

end Hypernets.Copying.AtomEquality.Different.Context

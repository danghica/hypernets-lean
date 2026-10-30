import Hypernets.Copying.SharingReadContext
import Hypernets.Copying.CommonContextExpansion
import Hypernets.Copying.CommonContextPrimitive
import Hypernets.Copying.CommonContextBoundary
import Hypernets.Copying.CopyTransport

/-! Exact normalization of the selected original read context into the
unchanged local dereference rule, retaining its complete sharing tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference.Context
open Graph Opening

/-- Reading a literal atom tree in the common frame is the original rule graph. -/
def graphIso {d h} (A : ContractionTree .atom (h+1)) :
    DeepIso (graph (A.atDepth d)) (before A d) := by
  have eq : family (A.atDepth d) = FillingWitness.liftedFamily (beforeFrame h) (beforeFill A) d := by
    cases d <;> funext e <;> cases e <;> simp only [family,Net.reboundary_refl] <;> rfl
  rw [graph,eq]
  exact FillingWitness.primitiveExpansionIso (beforeFrame h) (beforeFill A) d

variable {T : PreTemplate} {d h I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    {W : Hypernet d (List.replicate (h+1) .atom) [.atom]}
    (f : Occurrence W C) (reader inst store : C.Edge)
    (readerLabel : C.edgeLabel reader = primitiveLabel d (.operation (.unary .deref)))
    (instLabel : C.edgeLabel inst = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (t u v z o : C.Vertex)
    (readerSource : C.source reader = [t]) (readerTarget : C.target reader = [u])
    (instSource : C.source inst = [u]) (instTarget : C.target inst = [v])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v) (treeOutput : f.ports (.output 0) = z)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)))
    (A : ContractionTree .atom (h+1))
    (treeIso : DeepIso ((CommonContextCut.skeleton C f).expand
      (CommonContextCut.localFamily C f L)) (A.atDepth d))

/-- Original fillers of every selected component normalize separately: the
reader, instance and store are retained, and the actual sharing tree is kept. -/
noncomputable def componentIso (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    DeepIso
      ((CommonContextCut.skeleton C (components C f reader inst store readerLabel instLabel storeLabel e)).expand
        (CommonContextCut.localFamily C (components C f reader inst store readerLabel instLabel storeLabel e) L))
      (family (A.atDepth d) e) := by
  cases e with
  | tree =>
    exact (CommonContextCut.reboundarySourceIso C f L _ _).trans
      (CopyRule.reboundaryIso treeIso _ _)
  | reader =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f reader inst store readerLabel instLabel storeLabel .reader)
      (fun _ => ⟨.operation (.unary .deref),rfl,by intro h eq; cases eq⟩)
  | inst =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f reader inst store readerLabel instLabel storeLabel .inst)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | store =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f reader inst store readerLabel instLabel storeLabel .store)
      (fun _ => ⟨.store,rfl,by intro h eq; cases eq⟩)

/-- Regrouping the actual selected cut gives exactly the original complete
local read source, including every inactive sharing branch. -/
noncomputable def sourceIso : DeepIso
    ((CommonContextCut.skeleton C (occurrence C f reader inst store readerLabel instLabel storeLabel
      t u v z o readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput sharing)).expand
      (CommonContextCut.localFamily C (occurrence C f reader inst store readerLabel instLabel storeLabel
        t u v z o readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput sharing) L))
    (before A d) := by
  let last : DeepIso
      ((FillingWitness.liftedFrame (beforeFrame h) d).expand (fun e =>
        (CommonContextCut.skeleton C (components C f reader inst store readerLabel instLabel storeLabel e)).expand
          (CommonContextCut.localFamily C (components C f reader inst store readerLabel instLabel storeLabel e) L)))
      (graph (A.atDepth d)) :=
    Net.ExpansionIso.iso (FillingWitness.liftedFrame (beforeFrame h) d)
      (componentIso C cert f reader inst store readerLabel instLabel storeLabel A treeIso)
  exact (CommonContextCut.expansionIso C (FillingWitness.liftedFrame (beforeFrame h) d) (family W)
    (components C f reader inst store readerLabel instLabel storeLabel) (host C f t u v z o)
    (components_input C f reader inst store readerLabel instLabel storeLabel t u v z o
      readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput)
    (components_output C f reader inst store readerLabel instLabel storeLabel t u v z o
      readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput)
    (components_disjoint C f reader inst store readerLabel instLabel storeLabel sharing) L).trans
      (last.trans (graphIso A))

end Hypernets.Copying.Dereference.Context

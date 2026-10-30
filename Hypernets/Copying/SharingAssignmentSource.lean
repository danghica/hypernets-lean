import Hypernets.Copying.SharingAssignmentContext
import Hypernets.Copying.SharingReadSource

/-! Exact source normalization for original assignment around the complete
maximal sharing component and the unchanged stable value. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.Context
open Graph Opening

def graphIso {d h K} (A : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) :
    DeepIso (graph (A.atDepth d) G) (before A G) := by
  have eq : family (A.atDepth d) G = beforeFill A G := by
    cases d <;> funext e <;> cases e <;> simp only [family,Net.reboundary_refl] <;> rfl
  rw [graph,eq]
  exact DeepIso.refl _

variable {T : PreTemplate} {d h I O K} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    {W : Hypernet d (List.replicate (h+1) .atom) [.atom]} {G : Hypernet d [.term] K}
    (f : Occurrence W C) (g : Occurrence G C) (stable : Stable G)
    (assign inst store : C.Edge)
    (assignLabel : C.edgeLabel assign = primitiveLabel d (.operation (.binary .assign)))
    (instLabel : C.edgeLabel inst = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (t u v w z o : C.Vertex)
    (assignSource : C.source assign = [t]) (assignTarget : C.target assign = [u,w])
    (instSource : C.source inst = [u]) (instTarget : C.target inst = [v])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v) (treeOutput : f.ports (.output 0) = z)
    (valueInput : g.ports (.input 0) = w)
    (disjoint : ∀ a b, a ≠ b → ∀ e j,
      (components C f g assign inst store assignLabel instLabel storeLabel a).edges e ≠
      (components C f g assign inst store assignLabel instLabel storeLabel b).edges j)
    (A : ContractionTree .atom (h+1))
    (treeIso : DeepIso ((CommonContextCut.skeleton C f).expand
      (CommonContextCut.localFamily C f L)) (A.atDepth d))

noncomputable def componentIso (e : (beforePattern d h K).Edge) :
    DeepIso
      ((CommonContextCut.skeleton C (components C f g assign inst store assignLabel instLabel storeLabel e)).expand
        (CommonContextCut.localFamily C (components C f g assign inst store assignLabel instLabel storeLabel e) L))
      (family (A.atDepth d) G e) := by
  cases e with
  | tree =>
    exact (CommonContextCut.reboundarySourceIso C f L _ _).trans (CopyRule.reboundaryIso treeIso _ _)
  | value =>
    refine (CommonContextCut.reboundarySourceIso C g L _ _).trans (CopyRule.reboundaryIso ?_ _ _)
    apply CommonContextCut.primitive_leftIso C cert g
    intro e
    obtain ⟨p,label,allowed⟩ := stable.labels e
    exact ⟨p,label,by intro h eq; subst p; exact allowed⟩
  | assign =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g assign inst store assignLabel instLabel storeLabel .assign)
      (fun _ => ⟨.operation (.binary .assign),rfl,by intro h eq; cases eq⟩)
  | inst =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g assign inst store assignLabel instLabel storeLabel .inst)
      (fun _ => ⟨.instanceEdge,rfl,by intro h eq; cases eq⟩)
  | store =>
    exact CommonContextCut.primitive_leftIso C cert
      (components C f g assign inst store assignLabel instLabel storeLabel .store)
      (fun _ => ⟨.store,rfl,by intro h eq; cases eq⟩)

noncomputable def sourceIso : DeepIso
    ((CommonContextCut.skeleton C (occurrence C f g assign inst store assignLabel instLabel storeLabel
      t u v w z o assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput disjoint)).expand
      (CommonContextCut.localFamily C (occurrence C f g assign inst store assignLabel instLabel storeLabel
        t u v w z o assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput disjoint) L))
    (before A G) := by
  let last : DeepIso
      ((beforePattern d h K).expand (fun e =>
        (CommonContextCut.skeleton C (components C f g assign inst store assignLabel instLabel storeLabel e)).expand
          (CommonContextCut.localFamily C (components C f g assign inst store assignLabel instLabel storeLabel e) L)))
      (graph (A.atDepth d) G) :=
    Net.ExpansionIso.iso (beforePattern d h K)
      (componentIso C cert f g stable assign inst store assignLabel instLabel storeLabel A treeIso)
  exact (CommonContextCut.expansionIso C (beforePattern d h K) (family W G)
    (components C f g assign inst store assignLabel instLabel storeLabel) (host C f g t u v w z o)
    (components_input C f g assign inst store assignLabel instLabel storeLabel t u v w z o
      assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput)
    (components_output C f g assign inst store assignLabel instLabel storeLabel t u v w z o
      assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput)
    disjoint L).trans (last.trans (graphIso A G))

end Hypernets.Copying.Assignment.Context

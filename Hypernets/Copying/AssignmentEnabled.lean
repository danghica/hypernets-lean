import Hypernets.Copying.SharingAssignmentSource
import Hypernets.Copying.AllocationEnabled

/-! Reconstruct the unchanged assignment rule from its retained original
atom frame and the actual rooted stable operand. The operand's complete
corolla is selected independently, including a lambda inside a shallow family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined Opening

namespace Search.StableAt
/-- A stable source denotes an actual complete stable corolla occurrence,
with its own ordered output interface and exact original input attachment. -/
theorem occurrence {d I O} {C : Hypernet d I O} {v : C.Vertex}
    (ready : Search.StableAt C v) :
    ∃ K, ∃ G : Hypernet d [.term] K, ∃ f : Occurrence G C,
      Stable G ∧ f.ports (.input 0) = v := by
  obtain ⟨e,p,head,stable⟩ := ready
  let G := (primitiveNet d p).reboundary (Stable.primitive_input stable) rfl
  let f : Occurrence G C := (Occurrence.primitive C e head.1).reboundarySource
    (Stable.primitive_input stable) rfl
  refine ⟨_,G,f,?_,?_⟩
  · apply Stable.of_labels
    intro a
    exact ⟨p,by cases d <;> rfl,stable⟩
  · change C.sourcePort e _ = v
    have len : (C.source e).length = 1 := by
      rw [C.source_length,head.1,primitive_input,Stable.primitive_input stable]; rfl
    obtain ⟨w,row⟩ := List.length_eq_one_iff.mp len
    have same : v = w := by simpa only [row,List.mem_singleton] using head.2
    simpa [Net.sourcePort,row] using same.symm
end Search.StableAt

namespace Assignment
variable {d I O h} (C : Hypernet d I O) (tree : ContractionTree .atom (h+1))
    (f : Occurrence (tree.atDepth d) C)
    (assign inst store : C.Edge)
    (assignLabel : C.edgeLabel assign = primitiveLabel d (.operation (.binary .assign)))
    (instLabel : C.edgeLabel inst = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (t u v w z o : C.Vertex)
    (assignSource : C.source assign = [t]) (assignTarget : C.target assign = [u,w])
    (instSource : C.source inst = [u]) (instTarget : C.target inst = [v])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v) (treeOutput : f.ports (.output 0) = z)
include assignLabel instLabel storeLabel assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput

/-- The actual full original atom tree, instance and store, together with
rooted readiness of the new value, construct an original assignment rewrite.
No whole-value retention or matching/execution oracle is assumed. -/
theorem rooted_frame_enabled {i : Fin I.length}
    (rooted : Search.RootedFrom C i (.rewrite,t)) :
    ∃ H : Hypernet d I O, ∃ q, Rewrite C t H q := by
  have head : MatchEmbedding.HeadAt C t assign (.operation (.binary .assign)) :=
    ⟨assignLabel,by rw [assignSource]; exact List.mem_cons_self⟩
  have selected : (C.target assign)[1]? = some w := by rw [assignTarget]; rfl
  obtain ⟨K,G,g,stable,valueInput⟩ := (Search.rooted_rewrite_arguments rooted head 1 (by decide) w selected).occurrence
  have sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)) := by
    intro e
    rcases tree.labels e with weak | contraction
    · exact .inl (f.matchEmbedding.primitive e _ (congrArg (primitiveLabel d) weak))
    · exact .inr (.inl (f.matchEmbedding.primitive e _ (congrArg (primitiveLabel d) contraction)))
  let apart := Context.components_disjoint C f g assign inst store assignLabel instLabel storeLabel
    u w assignTarget instSource valueInput stable sharing
  let frame := Context.occurrence C f g assign inst store assignLabel instLabel storeLabel
    t u v w z o assignSource assignTarget instSource instTarget storeSource storeTarget
    treeInput treeOutput valueInput apart
  let actual : Occurrence (before tree G) C :=
    (Occurrence.ofIso (Context.graphIso tree G).symm).comp frame
  have attached : actual.ports (inputPort h K 0) = t := by
    cases d <;> rfl
  have step := actual.local_rewrite (.assign tree G stable)
  exact ⟨_,_,attached ▸ step⟩

end Assignment
end Hypernets.Copying

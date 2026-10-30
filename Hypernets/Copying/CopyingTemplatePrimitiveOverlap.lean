import Hypernets.Copying.CopyingTemplateForwardBarrier
import Hypernets.Copying.CopyingTemplateLeftLabels
import Hypernets.Copying.OperationalPrimitiveOverlap

/-! Every original non-boxed operational rule has a fully retained forward
footprint in a copying specimen. The argument is unrestricted: term-sharing
entry barriers and atom/store labels replace any binding-free hypothesis. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ForwardOverlap
open Graph Search.Expansion

/-- Operational footprints contain their head, atom sharing, a store, or an
adjacent stable operand. Term sharing is deliberately absent from this list. -/
def PrimitiveEdgeCase {d I O} (A : Hypernet d I O) (head e : A.Edge) : Prop :=
  e = head ∨
  (A.edgeLabel e = primitiveLabel d (.weakening .atom) ∨
    A.edgeLabel e = primitiveLabel d (.contraction .atom)) ∨
  A.edgeLabel e = primitiveLabel d .store ∨
  (A.Adjacent head e ∧ StableLabel d (A.edgeLabel e))

/-- Entire actual primitive matches avoid shallow copying holes. This includes
irrelevant atom-tree siblings and every edge of the original stable value. -/
theorem primitive_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L))
    {v : C.Vertex} (away : ¬ Entering C (.rewrite,v))
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand L))
    {a head p} (selected : MatchEmbedding.HeadAt A a head p)
    (attached : f.ports a = Net.Expansion.host C L v)
    (cases_ : ∀ e, PrimitiveEdgeCase A head e) :
    RetainedFootprint.AvoidsShallow C f := by
  have chosen : MatchEmbedding.HeadAt (C.expand L) (Net.Expansion.host C L v) (f.edges head) p := by
    rw [← attached]
    exact f.head selected
  obtain ⟨⟨copy⟩,_⟩ := BindingOverlap.head_retained C cert away chosen
  intro e h hole
  rcases cases_ e with rfl | share | store | ⟨adj,stable⟩
  · exact away ⟨_,h,hole,source_owner C L chosen.2⟩
  · have mapped := share.elim
      (fun label => Or.inl (f.primitive _ _ label))
      (fun label => Or.inr (f.primitive _ _ label))
    exact atom_sharing_not_hole C cert mapped h hole
  · exact store_not_hole C cert (f.primitive _ _ store) h hole
  · obtain ⟨w,target,source⟩ := f.adjacent adj
    obtain ⟨u,eq⟩ := copy.target_origin target
    apply source_not_hole C cert closed (eq ▸ source) _ h hole
    obtain ⟨p,label,allowed⟩ := stable
    intro bad
    have same := primitiveLabel_injective d ((f.primitive e p label).symm.trans bad)
    subst p
    exact allowed

/-- Allocation's outer graph consists exactly of its active reference head
and its original stable operand. -/
theorem allocation_cases {d O} (G : Hypernet d [.term] O) (stable : Stable G)
    (e : (Allocation.before G).Edge) : PrimitiveEdgeCase (Allocation.before G) (Allocation.head G) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left
    cases d
    all_goals
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      rfl
  | true =>
    right; right; right
    cases d
    all_goals
      refine ⟨⟨.internal (.inl (0 : Fin 1)),?_,?_⟩,stable.labels e⟩
      · exact List.mem_cons_self
      · exact List.mem_map_of_mem (Stable.input_source stable.labels e)

/-- A read inspects its head, instance, complete atom tree and store. -/
theorem read_cases {h} (T : ContractionTree .atom (h+1)) (d : Nat)
    (e : (Dereference.before T d).Edge) :
    PrimitiveEdgeCase (Dereference.before T d) (Dereference.localMatch T d).headEdge e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | reader =>
    left
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e
    rfl
  | inst =>
    right; right; right
    exact ⟨⟨.internal (.inl (0 : Fin 3)),List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | tree =>
    right; left
    exact (T.labels e).imp (congrArg (primitiveLabel d)) (congrArg (primitiveLabel d))
  | store => exact .inr (.inr (.inl rfl))

/-- Numeric unary computation inspects exactly its head and numeric operand. -/
theorem unary_cases (d n : Nat) (e : (Arithmetic.unaryBefore d n).Edge) :
    PrimitiveEdgeCase (Arithmetic.unaryBefore d n) (Arithmetic.unaryHead d n) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left
    cases d
    all_goals
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      rfl
  | true =>
    right; right; right
    cases d
    all_goals
      exact ⟨⟨.internal (.inl (0 : Fin 1)),List.mem_cons_self,List.mem_cons_self⟩,
        ⟨.operation (.const (.nat n)),rfl,rfl⟩⟩

/-- Binary arithmetic retains both ordered numeric operand occurrences. -/
theorem binary_cases (o : Arithmetic.BinaryCode) (d m n : Nat)
    (e : (Arithmetic.binaryBefore o d m n).Edge) :
    PrimitiveEdgeCase (Arithmetic.binaryBefore o d m n) (Arithmetic.binaryHead o d m n) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left
    cases d
    all_goals
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      rfl
  | true =>
    right; right; right
    cases d
    all_goals obtain ⟨side,e⟩ := e; cases side
    all_goals first
      | exact ⟨⟨.internal (.inl (0 : Fin 2)),List.mem_cons_self,List.mem_cons_self⟩,
          ⟨.operation (.const (.nat m)),rfl,rfl⟩⟩
      | exact ⟨⟨.internal (.inl (1 : Fin 2)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩,
          ⟨.operation (.const (.nat n)),rfl,rfl⟩⟩

/-- A write inspects its destination instance, the whole atom tree and store,
and every edge of the original stable new value. -/
theorem assignment_cases {d h O} (T : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] O) (stable : Stable G) (e : (Assignment.before T G).Edge) :
    PrimitiveEdgeCase (Assignment.before T G) (Assignment.localMatch T G).headEdge e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | assign =>
    left
    cases d
    all_goals
      have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e
      rfl
  | inst =>
    right; right; right
    cases d
    all_goals exact ⟨⟨.internal (.inl (0 : Fin 4)),List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | tree =>
    right; left
    cases d with
    | zero => exact (T.labels e).imp (congrArg (primitiveLabel 0)) (congrArg (primitiveLabel 0))
    | succ d => exact (T.labels e).imp (congrArg (primitiveLabel (d+1))) (congrArg (primitiveLabel (d+1)))
  | store => right; right; left; cases d <;> rfl
  | value =>
    right; right; right
    cases d
    all_goals
      refine ⟨⟨.internal (.inl (1 : Fin 4)),List.mem_cons_of_mem _ List.mem_cons_self,?_⟩,stable.labels e⟩
      exact List.mem_map_of_mem (Stable.input_source stable.labels e)

/-- Equality of two references to the same cell inspects both original
instances and all edges of the shared atom tree. -/
theorem same_cases {h} (T : ContractionTree .atom (h+2)) (d : Nat)
    (e : (AtomEquality.Same.before T d).Edge) :
    PrimitiveEdgeCase (AtomEquality.Same.before T d) ⟨.compare,(0 : Fin 1)⟩ e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | compare =>
    left
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e
    rfl
  | left =>
    right; right; right
    exact ⟨⟨.internal (.inl (0 : Fin 5)),List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | right =>
    right; right; right
    exact ⟨⟨.internal (.inl (1 : Fin 5)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | tree =>
    right; left
    exact (T.labels e).imp (congrArg (primitiveLabel d)) (congrArg (primitiveLabel d))
  | store => exact .inr (.inr (.inl rfl))

/-- Disequality inspects both separate original stores and both entire atom
trees, including branches unrelated to the selected references. -/
theorem different_cases {n m} (T : ContractionTree .atom (n+1))
    (U : ContractionTree .atom (m+1)) (d : Nat)
    (e : (AtomEquality.Different.before T U d).Edge) :
    PrimitiveEdgeCase (AtomEquality.Different.before T U d) ⟨.compare,(0 : Fin 1)⟩ e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | compare =>
    left
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e
    rfl
  | left =>
    right; right; right
    exact ⟨⟨.internal (.inl (0 : Fin 6)),List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | right =>
    right; right; right
    exact ⟨⟨.internal (.inl (1 : Fin 6)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩,
      ⟨.instanceEdge,rfl,trivial⟩⟩
  | tree =>
    right; left
    exact (T.labels e).imp (congrArg (primitiveLabel d)) (congrArg (primitiveLabel d))
  | treeRight =>
    right; left
    exact (U.labels e).imp (congrArg (primitiveLabel d)) (congrArg (primitiveLabel d))
  | store => exact .inr (.inr (.inl rfl))
  | storeRight => exact .inr (.inr (.inl rfl))

end Hypernets.Copying.CopyingTemplate.ForwardOverlap

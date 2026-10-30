import Hypernets.Copying.SharingReadContext
import Hypernets.Copying.SharingPrimitiveContext
import Hypernets.Copying.AssignmentReplacement

/-! The unchanged assignment frame around a maximal atom context and the
literal stable value embeds in the original shared context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.Context
open Graph Opening
variable {d h K}

def family (W : Hypernet d (List.replicate (h+1) .atom) [.atom]) (G : Hypernet d [.term] K)
    (e : (beforePattern d h K).Edge) : Hypernet d
      ((alphabet d).signature.input ((beforePattern d h K).edgeLabel e))
      ((alphabet d).signature.output ((beforePattern d h K).edgeLabel e)) := by
  cases e with
  | assign => exact Net.corolla (alphabet d).signature (primitiveLabel d (.operation (.binary .assign)))
  | inst => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | store => exact Net.corolla (alphabet d).signature (primitiveLabel d .store)
  | tree => exact W.reboundary (primitive_input d (.hole (treeHole h))).symm (primitive_output d (.hole (treeHole h))).symm
  | value => exact G.reboundary (primitive_input d (.hole (valueHole K))).symm (primitive_output d (.hole (valueHole K))).symm

def graph (W : Hypernet d (List.replicate (h+1) .atom) [.atom]) (G : Hypernet d [.term] K) :=
  (beforePattern d h K).expand (family W G)

variable {I O} (C : Hypernet d I O) {W : Hypernet d (List.replicate (h+1) .atom) [.atom]}
    {G : Hypernet d [.term] K} (f : Occurrence W C) (g : Occurrence G C)
    (assign inst store : C.Edge)
    (assignLabel : C.edgeLabel assign = primitiveLabel d (.operation (.binary .assign)))
    (instLabel : C.edgeLabel inst = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)

noncomputable def components (e : (beforePattern d h K).Edge) : Occurrence (family W G e) C := by
  cases e with
  | assign => exact Occurrence.labelledCorolla C assign _ assignLabel
  | inst => exact Occurrence.labelledCorolla C inst _ instLabel
  | store => exact Occurrence.labelledCorolla C store _ storeLabel
  | tree => exact f.reboundarySource (primitive_input d (.hole (treeHole h))).symm (primitive_output d (.hole (treeHole h))).symm
  | value => exact g.reboundarySource (primitive_input d (.hole (valueHole K))).symm (primitive_output d (.hole (valueHole K))).symm

variable (t u v w z o : C.Vertex)

def host : (beforePattern d h K).Vertex → C.Vertex
  | .input i => if zero : i.val = 0 then t else
      f.ports (.input ⟨i.val,by simpa [inputs] using i.isLt⟩)
  | .output i => if zero : i.val = 0 then o else
      g.ports (.output ⟨i.val-1,by have := i.isLt; simp only [outputs,List.length_cons] at this; omega⟩)
  | .internal i => if i.val = 0 then u else if i.val = 1 then w else if i.val = 2 then v else z

variable (assignSource : C.source assign = [t]) (assignTarget : C.target assign = [u,w])
    (instSource : C.source inst = [u]) (instTarget : C.target inst = [v])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v) (treeOutput : f.ports (.output 0) = z)
    (valueInput : g.ports (.input 0) = w)
include assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput

omit assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput in
private theorem sharing_ne {a : (alphabet d).Symbol} (sharing : SharingLabel d .atom a)
    {p : Primitive} (weak : p ≠ .weakening .atom) (contract : p ≠ .contraction .atom)
    (hole : ∀ h, p ≠ .hole h) : a ≠ primitiveLabel d p := by
  intro eq
  rcases sharing with w | c | ⟨h,n,label,_,_⟩
  · exact weak (primitiveLabel_injective d (eq.symm.trans w))
  · exact contract (primitiveLabel_injective d (eq.symm.trans c))
  · exact hole h (primitiveLabel_injective d (eq.symm.trans label))

include assignLabel storeLabel in
omit assignSource instTarget storeSource storeTarget treeInput treeOutput in
private theorem value_ne_nodes (stable : Stable G) (e : G.Edge) :
    g.edges e ≠ assign ∧ g.edges e ≠ inst ∧ g.edges e ≠ store := by
  obtain ⟨p,label,allowed⟩ := stable.labels e
  have actual := g.matchEmbedding.primitive e p label
  change C.edgeLabel (g.edges e) = primitiveLabel d p at actual
  refine ⟨?_,?_,?_⟩
  · intro eq
    rw [eq,assignLabel] at actual
    have same := primitiveLabel_injective d actual
    subst p
    cases allowed
  · intro eq
    have mem := g.matchEmbedding.source_mem (Stable.input_source stable.labels e)
    change g.ports (.input 0) ∈ C.source (g.edges e) at mem
    rw [eq,instSource,valueInput] at mem
    have same : w = u := List.mem_singleton.mp mem
    have nd := C.target_nodup assign
    rw [assignTarget] at nd
    exact (List.nodup_cons.mp nd).1 (by simp [same])
  · intro eq
    rw [eq,storeLabel] at actual
    have same := primitiveLabel_injective d actual
    subst p
    exact allowed

omit assignSource instTarget storeSource storeTarget treeInput treeOutput in
/-- Every component image is disjoint: the stable value remains the original
primitive footprint, and the two assignment argument ports are distinct. -/
theorem components_disjoint (stable : Stable G)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) :
    ∀ a b, a ≠ b → ∀ e j,
      (components C f g assign inst store assignLabel instLabel storeLabel a).edges e ≠
      (components C f g assign inst store assignLabel instLabel storeLabel b).edges j := by
  have stableNe (e : G.Edge) (a : W.Edge) : g.edges e ≠ f.edges a := by
    intro eq
    obtain ⟨p,label,allowed⟩ := stable.labels e
    have actual := g.matchEmbedding.primitive e p label
    change C.edgeLabel (g.edges e) = primitiveLabel d p at actual
    rw [eq] at actual
    exact sharing_ne (sharing a)
      (by intro h; subst p; exact allowed)
      (by intro h; subst p; exact allowed)
      (by intro h bad; subst p; exact allowed) actual
  have nodes := value_ne_nodes C g assign inst store assignLabel storeLabel
    u w assignTarget instSource valueInput stable
  intro a b ne e j eq
  cases a <;> cases b
  all_goals try exact ne rfl
  all_goals simp only [components,Occurrence.labelledCorolla_edges,Occurrence.reboundarySource] at eq
  all_goals first
    | exact (nodes e).1 eq
    | exact (nodes e).2.1 eq
    | exact (nodes e).2.2 eq
    | exact (nodes j).1 eq.symm
    | exact (nodes j).2.1 eq.symm
    | exact (nodes j).2.2 eq.symm
    | exact stableNe e j eq
    | exact stableNe j e eq.symm
    | skip
  all_goals have labels := congrArg C.edgeLabel eq
  all_goals first
    | (have same := primitiveLabel_injective d (assignLabel.symm.trans (labels.trans instLabel)); cases same)
    | (have same := primitiveLabel_injective d (assignLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (instLabel.symm.trans (labels.trans assignLabel)); cases same)
    | (have same := primitiveLabel_injective d (instLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans assignLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans instLabel)); cases same)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans assignLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans instLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans assignLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans instLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeLabel)

theorem components_input (e) (i) :
    (components C f g assign inst store assignLabel instLabel storeLabel e).ports (.input i) =
      host C f g t u v w z o ((beforePattern d h K).sourcePort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       simp only [components]
       rw [Occurrence.labelledCorolla_input]
       simp [Net.sourcePort,assignSource,instSource,storeSource,
         host,beforePattern,Net.relabel,beforeFrame,beforeSource,inputPort] <;> rfl)
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,beforePattern,
         Net.relabel,beforeFrame,beforeSource,host] using valueInput)
    | (change Fin (List.replicate (h+1) Wire.atom).length at i
       obtain ⟨i,hi⟩ := i
       have bound : i < h+1 := by simpa using hi
       by_cases zero : i = 0
       · subst i
         simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,beforePattern,
           Net.relabel,beforeFrame,beforeSource,host] using treeInput
       · have positive : ∃ j : Fin h, i = j.val+1 := by
           refine ⟨⟨i-1,by omega⟩,?_⟩; simp; omega
         obtain ⟨j,rfl⟩ := positive
         simp [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,beforePattern,
           Net.relabel,beforeFrame,beforeSource,otherInputs,inputPort,host])

theorem components_output (e) (i) :
    (components C f g assign inst store assignLabel instLabel storeLabel e).ports (.output i) =
      host C f g t u v w z o ((beforePattern d h K).targetPort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 2 at i
       have eq : i = 0 ∨ i = 1 := by omega
       rcases eq with rfl | rfl
       all_goals simp only [components]
       all_goals rw [Occurrence.labelledCorolla_output]
       all_goals simp [Net.targetPort,assignTarget,host,beforePattern,Net.relabel,beforeFrame,beforeTarget])
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       first
       | (change f.ports (.output 0) = z; exact treeOutput)
       | (simp only [components]
          rw [Occurrence.labelledCorolla_output]
          simp [Net.targetPort,instTarget,storeTarget,host,beforePattern,Net.relabel,beforeFrame,beforeTarget]))
    | (change Fin K.length at i
       simp [components,Occurrence.reboundarySource,Port.cast,Net.targetPort,beforePattern,
         Net.relabel,beforeFrame,beforeTarget,valueOutputs,outputPort,host])

/-- The full raw assignment frame embeds once its actual component edge
images have been shown disjoint by original matching. -/
noncomputable def occurrence
    (disjoint : ∀ a b, a ≠ b → ∀ e j,
      (components C f g assign inst store assignLabel instLabel storeLabel a).edges e ≠
      (components C f g assign inst store assignLabel instLabel storeLabel b).edges j) :
    Occurrence (graph W G) C :=
  Occurrence.ExpansionJoin.occurrence (beforePattern d h K) (family W G)
    (components C f g assign inst store assignLabel instLabel storeLabel) (host C f g t u v w z o)
    (components_input C f g assign inst store assignLabel instLabel storeLabel t u v w z o
      assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput)
    (components_output C f g assign inst store assignLabel instLabel storeLabel t u v w z o
      assignSource assignTarget instSource instTarget storeSource storeTarget treeInput treeOutput valueInput) disjoint

end Hypernets.Copying.Assignment.Context

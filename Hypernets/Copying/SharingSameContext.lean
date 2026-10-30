import Hypernets.Copying.SharingReadContext

/-! Same-store equality with one complete original sharing context and two
ordered instance entries. The comparison and store nodes remain literal. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Same.Context
open Graph Opening
variable {d h}
private theorem val3 : (3 : Fin 5).val = 3 := rfl
private theorem val4 : (4 : Fin 5).val = 4 := rfl

def family (W : Hypernet d (List.replicate (h+2) .atom) [.atom])
    (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    Hypernet d ((alphabet d).signature.input ((FillingWitness.liftedFrame (beforeFrame h) d).edgeLabel e))
      ((alphabet d).signature.output ((FillingWitness.liftedFrame (beforeFrame h) d).edgeLabel e)) := by
  cases e with
  | compare => exact Net.corolla (alphabet d).signature (primitiveLabel d (.operation (.binary .atomEq)))
  | left => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | right => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | store => exact Net.corolla (alphabet d).signature (primitiveLabel d .store)
  | tree => exact W.reboundary (primitive_input d (.hole (treeHole h))).symm (primitive_output d (.hole (treeHole h))).symm

def graph (W : Hypernet d (List.replicate (h+2) .atom) [.atom]) : Hypernet d (inputs h) [.term] :=
  (FillingWitness.liftedFrame (beforeFrame h) d).expand (family W)

variable {I O} (C : Hypernet d I O) {W : Hypernet d (List.replicate (h+2) .atom) [.atom]}
    (f : Occurrence W C) (compare first second store : C.Edge)
    (compareLabel : C.edgeLabel compare = primitiveLabel d (.operation (.binary .atomEq)))
    (firstLabel : C.edgeLabel first = primitiveLabel d .instanceEdge)
    (secondLabel : C.edgeLabel second = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)

noncomputable def components (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    Occurrence (family W e) C := by
  cases e with
  | compare => exact Occurrence.labelledCorolla C compare _ compareLabel
  | left => exact Occurrence.labelledCorolla C first _ firstLabel
  | right => exact Occurrence.labelledCorolla C second _ secondLabel
  | store => exact Occurrence.labelledCorolla C store _ storeLabel
  | tree => exact f.reboundarySource (primitive_input d (.hole (treeHole h))).symm (primitive_output d (.hole (treeHole h))).symm

private theorem sharing_ne {a : (alphabet d).Symbol} (sharing : SharingLabel d .atom a)
    {p : Primitive} (weak : p ≠ .weakening .atom) (contract : p ≠ .contraction .atom)
    (hole : ∀ h, p ≠ .hole h) : a ≠ primitiveLabel d p := by
  intro eq
  rcases sharing with w | c | ⟨h,n,label,_,_⟩
  · exact weak (primitiveLabel_injective d (eq.symm.trans w))
  · exact contract (primitiveLabel_injective d (eq.symm.trans c))
  · exact hole h (primitiveLabel_injective d (eq.symm.trans label))

theorem components_disjoint (distinct : first ≠ second)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) :
    ∀ a b, a ≠ b → ∀ e g,
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel a).edges e ≠
      (components C f compare first second store compareLabel firstLabel secondLabel storeLabel b).edges g := by
  intro a b ne e g eq
  cases a <;> cases b
  all_goals try exact ne rfl
  all_goals simp only [components,Occurrence.labelledCorolla_edges,Occurrence.reboundarySource] at eq
  all_goals try exact distinct eq
  all_goals try exact distinct eq.symm
  all_goals have labels := congrArg C.edgeLabel eq
  all_goals first
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans firstLabel)); cases same)
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans secondLabel)); cases same)
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (firstLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (secondLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (firstLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (secondLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans firstLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans secondLabel)); cases same)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans compareLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans firstLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans secondLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans compareLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans firstLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans secondLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeLabel)

variable (t u u' v v' z o : C.Vertex)

def host : (FillingWitness.liftedFrame (beforeFrame h) d).Vertex → C.Vertex
  | .input i => if zero : i.val = 0 then t else
      f.ports (.input ⟨i.val+1,by have := i.isLt; simp [inputs] at *; omega⟩)
  | .output _ => o
  | .internal i => if i.val = 0 then u else if i.val = 1 then u' else
      if i.val = 2 then v else if i.val = 3 then v' else z

variable (compareSource : C.source compare = [t]) (compareTarget : C.target compare = [u,u'])
    (firstSource : C.source first = [u]) (firstTarget : C.target first = [v])
    (secondSource : C.source second = [u']) (secondTarget : C.target second = [v'])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v)
    (treeSecond : f.ports (.input ⟨1,by simp⟩) = v')
    (treeOutput : f.ports (.output 0) = z)
include compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput

theorem components_input (e) (i) :
    (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e).ports (.input i) =
      host C f t u u' v v' z o ((FillingWitness.liftedFrame (beforeFrame h) d).sourcePort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       simp only [components]
       rw [Occurrence.labelledCorolla_input]
       simp [Net.sourcePort,compareSource,firstSource,secondSource,storeSource,
         host,FillingWitness.liftedFrame,Net.relabel,beforeFrame,beforeSource,inputPort,val4])
    | (change Fin (List.replicate (h+2) Wire.atom).length at i
       obtain ⟨i,hi⟩ := i
       have bound : i < h+2 := by simpa using hi
       by_cases zero : i = 0
       · subst i
         simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,host,val3,val4] using treeInput
       · by_cases one : i = 1
         · subst i
           simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
             Net.relabel,beforeFrame,beforeSource,host,val3,val4] using treeSecond
         · have positive : ∃ j : Fin h, i = j.val+2 := by
             refine ⟨⟨i-2,by omega⟩,?_⟩; simp; omega
           obtain ⟨j,rfl⟩ := positive
           simp [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
             Net.relabel,beforeFrame,beforeSource,otherInputs,inputPort,host])

theorem components_output (e) (i) :
    (components C f compare first second store compareLabel firstLabel secondLabel storeLabel e).ports (.output i) =
      host C f t u u' v v' z o ((FillingWitness.liftedFrame (beforeFrame h) d).targetPort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 2 at i
       have choices : i = 0 ∨ i = 1 := by omega
       rcases choices with rfl | rfl
       all_goals
         simp only [components]
         rw [Occurrence.labelledCorolla_output]
         simp [Net.targetPort,compareTarget,host,FillingWitness.liftedFrame,Net.relabel,beforeFrame,beforeTarget])
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       first
       | simpa [components,Occurrence.reboundarySource,Port.cast,Net.targetPort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeTarget,host,val3,val4] using treeOutput
       | (simp only [components]
          rw [Occurrence.labelledCorolla_output]
          simp [Net.targetPort,firstTarget,secondTarget,storeTarget,host,FillingWitness.liftedFrame,
            Net.relabel,beforeFrame,beforeTarget,val3]))

noncomputable def occurrence (distinct : first ≠ second)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) : Occurrence (graph W) C :=
  Occurrence.ExpansionJoin.occurrence (FillingWitness.liftedFrame (beforeFrame h) d) (family W)
    (components C f compare first second store compareLabel firstLabel secondLabel storeLabel)
    (host C f t u u' v v' z o)
    (components_input C f compare first second store compareLabel firstLabel secondLabel storeLabel
      t u u' v v' z o compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput)
    (components_output C f compare first second store compareLabel firstLabel secondLabel storeLabel
      t u u' v v' z o compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget treeInput treeSecond treeOutput)
    (components_disjoint C f compare first second store compareLabel firstLabel secondLabel storeLabel distinct sharing)

end Hypernets.Copying.AtomEquality.Same.Context

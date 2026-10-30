import Hypernets.Copying.SharingReadContext

/-! Different-store equality with two disjoint complete original sharing contexts.
The comparison, both instance entries and both store nodes remain literal. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Different.Context
open Graph Opening
variable {d n m}
private theorem val3 : (3 : Fin 6).val = 3 := rfl
private theorem val4 : (4 : Fin 6).val = 4 := rfl
private theorem val5 : (5 : Fin 6).val = 5 := rfl

def family (W : Hypernet d (List.replicate (n+1) .atom) [.atom])
    (V : Hypernet d (List.replicate (m+1) .atom) [.atom])
    (e : (FillingWitness.liftedFrame (beforeFrame n m) d).Edge) :
    Hypernet d ((alphabet d).signature.input ((FillingWitness.liftedFrame (beforeFrame n m) d).edgeLabel e))
      ((alphabet d).signature.output ((FillingWitness.liftedFrame (beforeFrame n m) d).edgeLabel e)) := by
  cases e with
  | compare => exact Net.corolla (alphabet d).signature (primitiveLabel d (.operation (.binary .atomEq)))
  | left => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | right => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | store => exact Net.corolla (alphabet d).signature (primitiveLabel d .store)
  | storeRight => exact Net.corolla (alphabet d).signature (primitiveLabel d .store)
  | treeRight => exact V.reboundary (primitive_input d (.hole (treeHole m 1))).symm (primitive_output d (.hole (treeHole m 1))).symm
  | tree => exact W.reboundary (primitive_input d (.hole (treeHole n 0))).symm (primitive_output d (.hole (treeHole n 0))).symm

def graph (W : Hypernet d (List.replicate (n+1) .atom) [.atom])
    (V : Hypernet d (List.replicate (m+1) .atom) [.atom]) : Hypernet d (inputs n m) [.term,.term] :=
  (FillingWitness.liftedFrame (beforeFrame n m) d).expand (family W V)

variable {I O} (C : Hypernet d I O) {W : Hypernet d (List.replicate (n+1) .atom) [.atom]}
    {V : Hypernet d (List.replicate (m+1) .atom) [.atom]}
    (f : Occurrence W C) (g : Occurrence V C) (compare first second store storeRight : C.Edge)
    (compareLabel : C.edgeLabel compare = primitiveLabel d (.operation (.binary .atomEq)))
    (firstLabel : C.edgeLabel first = primitiveLabel d .instanceEdge)
    (secondLabel : C.edgeLabel second = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (storeRightLabel : C.edgeLabel storeRight = primitiveLabel d .store)

noncomputable def components (e : (FillingWitness.liftedFrame (beforeFrame n m) d).Edge) :
    Occurrence (family W V e) C := by
  cases e with
  | compare => exact Occurrence.labelledCorolla C compare _ compareLabel
  | left => exact Occurrence.labelledCorolla C first _ firstLabel
  | right => exact Occurrence.labelledCorolla C second _ secondLabel
  | store => exact Occurrence.labelledCorolla C store _ storeLabel
  | storeRight => exact Occurrence.labelledCorolla C storeRight _ storeRightLabel
  | treeRight => exact g.reboundarySource (primitive_input d (.hole (treeHole m 1))).symm (primitive_output d (.hole (treeHole m 1))).symm
  | tree => exact f.reboundarySource (primitive_input d (.hole (treeHole n 0))).symm (primitive_output d (.hole (treeHole n 0))).symm

private theorem sharing_ne {a : (alphabet d).Symbol} (sharing : SharingLabel d .atom a)
    {p : Primitive} (weak : p ≠ .weakening .atom) (contract : p ≠ .contraction .atom)
    (hole : ∀ h, p ≠ .hole h) : a ≠ primitiveLabel d p := by
  intro eq
  rcases sharing with w | c | ⟨h,n,label,_,_⟩
  · exact weak (primitiveLabel_injective d (eq.symm.trans w))
  · exact contract (primitiveLabel_injective d (eq.symm.trans c))
  · exact hole h (primitiveLabel_injective d (eq.symm.trans label))

theorem components_disjoint (distinct : first ≠ second) (stores : store ≠ storeRight)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)))
    (sharingRight : ∀ e, SharingLabel d .atom (C.edgeLabel (g.edges e)))
    (apart : ∀ e j, f.edges e ≠ g.edges j) :
    ∀ a b, a ≠ b → ∀ e j,
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel a).edges e ≠
      (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel b).edges j := by
  intro a b ne e j eq
  cases a <;> cases b
  all_goals try exact ne rfl
  all_goals simp only [components,Occurrence.labelledCorolla_edges,Occurrence.reboundarySource] at eq
  all_goals try exact distinct eq
  all_goals try exact distinct eq.symm
  all_goals try exact stores eq
  all_goals try exact stores eq.symm
  all_goals try exact apart e j eq
  all_goals try exact apart j e eq.symm
  all_goals have labels := congrArg C.edgeLabel eq
  all_goals first
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans firstLabel)); cases same)
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans secondLabel)); cases same)
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (compareLabel.symm.trans (labels.trans storeRightLabel)); cases same)
    | (have same := primitiveLabel_injective d (firstLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (firstLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (firstLabel.symm.trans (labels.trans storeRightLabel)); cases same)
    | (have same := primitiveLabel_injective d (secondLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (secondLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (secondLabel.symm.trans (labels.trans storeRightLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans firstLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans secondLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeRightLabel.symm.trans (labels.trans compareLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeRightLabel.symm.trans (labels.trans firstLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeRightLabel.symm.trans (labels.trans secondLabel)); cases same)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans compareLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans firstLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans secondLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeRightLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans compareLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans firstLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans secondLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeLabel)
    | exact sharing_ne (sharing j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeRightLabel)
    | exact sharing_ne (sharingRight e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans compareLabel)
    | exact sharing_ne (sharingRight e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans firstLabel)
    | exact sharing_ne (sharingRight e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans secondLabel)
    | exact sharing_ne (sharingRight e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeLabel)
    | exact sharing_ne (sharingRight e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeRightLabel)
    | exact sharing_ne (sharingRight j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans compareLabel)
    | exact sharing_ne (sharingRight j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans firstLabel)
    | exact sharing_ne (sharingRight j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans secondLabel)
    | exact sharing_ne (sharingRight j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeLabel)
    | exact sharing_ne (sharingRight j) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeRightLabel)

variable (t u u' v v' z z' o o' : C.Vertex)

def host : (FillingWitness.liftedFrame (beforeFrame n m) d).Vertex → C.Vertex
  | .input i => if zero : i.val = 0 then t else
      if left : i.val ≤ n then f.ports (.input ⟨i.val,by simp; omega⟩)
      else g.ports (.input ⟨i.val-n,by have := i.isLt; simp [inputs] at *; omega⟩)
  | .output i => if i.val = 0 then o else o'
  | .internal i => if i.val = 0 then u else if i.val = 1 then u' else
      if i.val = 2 then v else if i.val = 3 then v' else if i.val = 4 then z else z'

variable (compareSource : C.source compare = [t]) (compareTarget : C.target compare = [u,u'])
    (firstSource : C.source first = [u]) (firstTarget : C.target first = [v])
    (secondSource : C.source second = [u']) (secondTarget : C.target second = [v'])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (storeRightSource : C.source storeRight = [z']) (storeRightTarget : C.target storeRight = [o'])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v)
    (treeSecond : g.ports (.input ⟨0,by simp⟩) = v')
    (treeOutput : f.ports (.output 0) = z)
    (treeRightOutput : g.ports (.output 0) = z')
include compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput

theorem components_input (e) (i) :
    (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e).ports (.input i) =
      host C f g t u u' v v' z z' o o' ((FillingWitness.liftedFrame (beforeFrame n m) d).sourcePort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       simp only [components]
       rw [Occurrence.labelledCorolla_input]
       simp [Net.sourcePort,compareSource,firstSource,secondSource,storeSource,storeRightSource,
         host,FillingWitness.liftedFrame,Net.relabel,beforeFrame,beforeSource,inputPort,val4,val5])
    | (change Fin (List.replicate (n+1) Wire.atom).length at i
       obtain ⟨i,hi⟩ := i
       have bound : i < n+1 := by simpa using hi
       cases i with
       | zero => simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,host] using treeInput
       | succ j =>
         simp [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,leftInputs,inputPort,host,show j+1 ≤ n by omega])
    | (change Fin (List.replicate (m+1) Wire.atom).length at i
       obtain ⟨i,hi⟩ := i
       have bound : i < m+1 := by simpa using hi
       cases i with
       | zero => simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,host,val3] using treeSecond
       | succ j =>
         simp [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,rightInputs,inputPort,host,show ¬n+(j+1) ≤ n by omega,Nat.add_assoc])

theorem components_output (e) (i) :
    (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel e).ports (.output i) =
      host C f g t u u' v v' z z' o o' ((FillingWitness.liftedFrame (beforeFrame n m) d).targetPort e i) := by
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
           Net.relabel,beforeFrame,beforeTarget,host,val4] using treeOutput
       | simpa [components,Occurrence.reboundarySource,Port.cast,Net.targetPort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeTarget,host,val3,val4,val5] using treeRightOutput
       | (simp only [components]
          rw [Occurrence.labelledCorolla_output]
          simp [Net.targetPort,firstTarget,secondTarget,storeTarget,storeRightTarget,host,FillingWitness.liftedFrame,
            Net.relabel,beforeFrame,beforeTarget,val3]))

noncomputable def occurrence (distinct : first ≠ second) (stores : store ≠ storeRight)
    (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e)))
    (sharingRight : ∀ e, SharingLabel d .atom (C.edgeLabel (g.edges e)))
    (apart : ∀ e j, f.edges e ≠ g.edges j) : Occurrence (graph W V) C :=
  Occurrence.ExpansionJoin.occurrence (FillingWitness.liftedFrame (beforeFrame n m) d) (family W V)
    (components C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel)
    (host C f g t u u' v v' z z' o o')
    (components_input C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel
      t u u' v v' z z' o o' compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput)
    (components_output C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel
      t u u' v v' z z' o o' compareSource compareTarget firstSource firstTarget secondSource secondTarget storeSource storeTarget storeRightSource storeRightTarget treeInput treeSecond treeOutput treeRightOutput)
    (components_disjoint C f g compare first second store storeRight compareLabel firstLabel secondLabel storeLabel storeRightLabel distinct stores sharing sharingRight apart)

end Hypernets.Copying.AtomEquality.Different.Context

import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.SharingTreeResiduals
import Hypernets.Copying.ExpansionOccurrenceJoin
import Hypernets.Copying.SharingBasin

/-! The literal dereference frame admits an arbitrary sharing-tree context,
including its original template holes, and embeds at its actual store nodes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference.Context
open Graph Opening
variable {d h}

/-- Keep the literal read/instance/store frame and fill only its tree slot. -/
def family (W : Hypernet d (List.replicate (h+1) .atom) [.atom])
    (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    Hypernet d ((alphabet d).signature.input ((FillingWitness.liftedFrame (beforeFrame h) d).edgeLabel e))
      ((alphabet d).signature.output ((FillingWitness.liftedFrame (beforeFrame h) d).edgeLabel e)) := by
  cases e with
  | reader => exact Net.corolla (alphabet d).signature (primitiveLabel d (.operation (.unary .deref)))
  | inst => exact Net.corolla (alphabet d).signature (primitiveLabel d .instanceEdge)
  | store => exact Net.corolla (alphabet d).signature (primitiveLabel d .store)
  | tree => exact W.reboundary (primitive_input d (.hole (treeHole h))).symm (primitive_output d (.hole (treeHole h))).symm

def graph (W : Hypernet d (List.replicate (h+1) .atom) [.atom]) : Hypernet d (inputs h) [.term] :=
  (FillingWitness.liftedFrame (beforeFrame h) d).expand (family W)

/-- This is exactly the original common context used by the read-source witness. -/
theorem witness_context {T : PreTemplate} {A B : ContractionTree .atom (h+1)}
    (w : FillingWitness T (A.atDepth d) (B.atDepth d)) :
    w.sharingReadBefore.context = graph w.context := by
  cases d
  all_goals
    apply congrArg (Net.expand (FillingWitness.liftedFrame (beforeFrame h) _))
    funext e
    cases e <;> simp only [family,Net.reboundary_refl] <;> rfl

variable {I O} (C : Hypernet d I O) {W : Hypernet d (List.replicate (h+1) .atom) [.atom]}
    (f : Occurrence W C) (reader inst store : C.Edge)
    (readerLabel : C.edgeLabel reader = primitiveLabel d (.operation (.unary .deref)))
    (instLabel : C.edgeLabel inst = primitiveLabel d .instanceEdge)
    (storeLabel : C.edgeLabel store = primitiveLabel d .store)

noncomputable def components (e : (FillingWitness.liftedFrame (beforeFrame h) d).Edge) :
    Occurrence (family W e) C := by
  cases e with
  | reader => exact Occurrence.labelledCorolla C reader _ readerLabel
  | inst => exact Occurrence.labelledCorolla C inst _ instLabel
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

/-- Sharing components and the three distinct primitive read interactions
have disjoint actual edge images, derived solely from their original labels. -/
theorem components_disjoint (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) :
    ∀ a b, a ≠ b → ∀ e g,
      (components C f reader inst store readerLabel instLabel storeLabel a).edges e ≠
      (components C f reader inst store readerLabel instLabel storeLabel b).edges g := by
  intro a b ne e g eq
  cases a <;> cases b
  all_goals try exact ne rfl
  all_goals simp only [components,Occurrence.labelledCorolla_edges,Occurrence.reboundarySource] at eq
  all_goals have labels := congrArg C.edgeLabel eq
  all_goals first
    | (have same := primitiveLabel_injective d (readerLabel.symm.trans (labels.trans instLabel)); cases same)
    | (have same := primitiveLabel_injective d (readerLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (instLabel.symm.trans (labels.trans readerLabel)); cases same)
    | (have same := primitiveLabel_injective d (instLabel.symm.trans (labels.trans storeLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans readerLabel)); cases same)
    | (have same := primitiveLabel_injective d (storeLabel.symm.trans (labels.trans instLabel)); cases same)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans readerLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans instLabel)
    | exact sharing_ne (sharing e) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.trans storeLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans readerLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans instLabel)
    | exact sharing_ne (sharing g) (by intro h; cases h) (by intro h; cases h) (by intro h eq; cases eq) (labels.symm.trans storeLabel)

variable (t u v z o : C.Vertex)

/-- The old term input and unused atom inputs are kept in their literal order. -/
def host : (FillingWitness.liftedFrame (beforeFrame h) d).Vertex → C.Vertex
  | .input i => if zero : i.val = 0 then t else
      f.ports (.input ⟨i.val,by simpa [inputs] using i.isLt⟩)
  | .output _ => o
  | .internal i => if i.val = 0 then u else if i.val = 1 then v else z

variable (readerSource : C.source reader = [t]) (readerTarget : C.target reader = [u])
    (instSource : C.source inst = [u]) (instTarget : C.target inst = [v])
    (storeSource : C.source store = [z]) (storeTarget : C.target store = [o])
    (treeInput : f.ports (.input ⟨0,by simp⟩) = v) (treeOutput : f.ports (.output 0) = z)
include readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput

theorem components_input (e) (i) :
    (components C f reader inst store readerLabel instLabel storeLabel e).ports (.input i) =
      host C f t u v z o ((FillingWitness.liftedFrame (beforeFrame h) d).sourcePort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 1 at i
       have eq : i = 0 := Subsingleton.elim _ _
       subst i
       simp only [components]
       rw [Occurrence.labelledCorolla_input]
       simp [Net.sourcePort,readerSource,instSource,storeSource,
         host,FillingWitness.liftedFrame,Net.relabel,beforeFrame,beforeSource,inputPort])
    | (change Fin (List.replicate (h+1) Wire.atom).length at i
       obtain ⟨i,hi⟩ := i
       have bound : i < h+1 := by simpa using hi
       by_cases zero : i = 0
       · subst i
         simpa [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,host] using treeInput
       · have positive : ∃ j : Fin h, i = j.val+1 := by
           refine ⟨⟨i-1,by omega⟩,?_⟩
           simp; omega
         obtain ⟨j,rfl⟩ := positive
         simp [components,Occurrence.reboundarySource,Port.cast,Net.sourcePort,FillingWitness.liftedFrame,
           Net.relabel,beforeFrame,beforeSource,otherInputs,inputPort,host])

theorem components_output (e) (i) :
    (components C f reader inst store readerLabel instLabel storeLabel e).ports (.output i) =
      host C f t u v z o ((FillingWitness.liftedFrame (beforeFrame h) d).targetPort e i) := by
  cases d <;> cases e
  all_goals change Fin 1 at i
  all_goals have eq : i = 0 := Subsingleton.elim _ _
  all_goals subst i
  all_goals first
    | (simpa [components,Occurrence.reboundarySource,Port.cast,Net.targetPort,FillingWitness.liftedFrame,
         Net.relabel,beforeFrame,beforeTarget,host] using treeOutput)
    | (simp only [components]
       rw [Occurrence.labelledCorolla_output]
       simp [Net.targetPort,readerTarget,instTarget,storeTarget,
         host,FillingWitness.liftedFrame,Net.relabel,beforeFrame,beforeTarget])

/-- The complete read-source common context embeds into the actual original
host, including every selected sharing hole and unused atom input. -/
noncomputable def occurrence (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) :
    Occurrence (graph W) C :=
  Occurrence.ExpansionJoin.occurrence (FillingWitness.liftedFrame (beforeFrame h) d) (family W)
    (components C f reader inst store readerLabel instLabel storeLabel) (host C f t u v z o)
    (components_input C f reader inst store readerLabel instLabel storeLabel t u v z o
      readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput)
    (components_output C f reader inst store readerLabel instLabel storeLabel t u v z o
      readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput)
    (components_disjoint C f reader inst store readerLabel instLabel storeLabel sharing)

theorem occurrence_input (sharing : ∀ e, SharingLabel d .atom (C.edgeLabel (f.edges e))) :
    (occurrence C f reader inst store readerLabel instLabel storeLabel t u v z o
      readerSource readerTarget instSource instTarget storeSource storeTarget treeInput treeOutput sharing).ports
      (.input ⟨0,by simp [inputs]⟩) = t := rfl

end Hypernets.Copying.Dereference.Context

import Hypernets.Copying.TargetSwapHostExpansion
import Hypernets.Copying.RetainedPrimitiveReplacement
import Hypernets.Copying.AssignmentCoherence

/-! The canonical assignment changes only two original target attachments
and the retained assignment head. Every operand component, including an
entire shallow lambda family, is retained as an original residual filling. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.Retained
open Graph Combined
variable {d I O} (C : Hypernet d I O) {v : C.Vertex} (m : Match C v)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (n : Match (C.expand F) (Net.Expansion.host C F v))
    (newValue : n.newValue = Net.Expansion.host C F m.newValue)
    (oldValue : n.oldValue = Net.Expansion.host C F m.oldValue)

/-- The actual canonical target swap agrees with the swap in the original
common context, preserving all old edge and vertex names exactly. -/
noncomputable def swapIso : DeepIso n.swapped (m.swapped.expand F) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := labelEquiv_refl d ((C.expand F).edgeLabel e)
  source e := by
    exact (DeepIso.ofIso (TargetSwap.HostExpansion.iso C F m.newValue m.oldValue
      m.new_not_input m.old_not_input m.values_typed)).source e
  target e := by
    have target := (DeepIso.ofIso (TargetSwap.HostExpansion.iso C F m.newValue m.oldValue
      m.new_not_input m.old_not_input m.values_typed)).target e
    change (((C.expand F).target e).map (TargetSwap.exchange n.newValue n.oldValue)).map
      (Port.map id) = _
    rw [newValue,oldValue]
    exact target

variable (copy : LabelCopy (F m.headEdge) (C.edgeLabel m.headEdge))
    (headEdge : n.headEdge = ⟨m.headEdge,copy.edge⟩)

/-- The entire common write reduct is assembled from the target-swapped
original context and a single replacement by unit and both weakenings. -/
noncomputable abbrev family := RetainedReplacement.family m.swapped (F := F) m.headEdge m.filler

/-- Both the complete graph and resumed token of the actual canonical write
agree with this original-context construction. -/
noncomputable def canonicalIso : StateIso n.canonical
    ⟨m.swapped.expand (family C m F),
      (.search,Net.Expansion.host m.swapped (family C m F) v)⟩ := by
  let f := swapIso C m F n newValue oldValue
  let i : Fin ((alphabet d).signature.input (C.edgeLabel m.headEdge)).length :=
    ⟨0,by rw [m.head.1,primitive_input]; decide⟩
  have input : m.swapped.sourcePort m.headEdge i = v := by
    have row := Search.operation_source m.head.1 m.head.2
    change C.sourcePort m.headEdge i = v
    simp [Net.sourcePort,row,i]
  have moved := Replacement.rename f n.headEdge n.filler (Net.Expansion.host C F v)
  have hostEq : Net.Expansion.host C F v = Net.Expansion.host m.swapped F v := by cases v <;> rfl
  have moved' : StateIso n.canonical
      (Replacement.state (m.swapped.expand F) n.headEdge n.filler
        (Net.Expansion.host m.swapped F v)) := by
    simpa only [Match.canonical,f,swapIso,Bijection.refl,Port.map_id_fun,id_eq,
      Net.reboundary_refl,hostEq] using moved
  have rehead (a : (C.expand F).Edge) (eq : a = ⟨m.headEdge,copy.edge⟩)
      (label : (C.expand F).edgeLabel a = primitiveLabel d (.operation (.binary .assign))) :
      Replacement.state (m.swapped.expand F) a
        ((DiscardResult.net d .unit).reboundary
          (by change [Wire.term] = (alphabet d).signature.input ((C.expand F).edgeLabel a); rw [label,primitive_input]; rfl)
          (by change [Wire.term,Wire.term] = (alphabet d).signature.output ((C.expand F).edgeLabel a); rw [label,primitive_output]; rfl))
        (Net.Expansion.host m.swapped F v) =
      Replacement.state (m.swapped.expand F) ⟨m.headEdge,copy.edge⟩
        (m.filler.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm)
        (Net.Expansion.host m.swapped F v) := by
    subst a
    unfold Match.filler
    rw [reboundary_comp]
  have normalized : StateIso n.canonical
      (Replacement.state (m.swapped.expand F) ⟨m.headEdge,copy.edge⟩
        (m.filler.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm)
        (Net.Expansion.host m.swapped F v)) :=
    moved'.trans (StateIso.ofEq (rehead n.headEdge headEdge n.head.1))
  have last := RetainedReplacement.canonicalIso m.swapped m.headEdge m.filler copy i
  have resumed : StateIso
      (Replacement.state (m.swapped.expand F) ⟨m.headEdge,copy.edge⟩
        (m.filler.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm)
        (Net.Expansion.host m.swapped F v))
      ⟨m.swapped.expand (family C m F),
        (.search,Net.Expansion.host m.swapped (family C m F) v)⟩ := by
    simpa only [Net.Expansion.insert,input] using last
  exact normalized.trans resumed


/-- The canonical write replacement consists only of unit and two term
weakenings, hence is focus-free at every depth. -/
theorem filler_free : FocusFree m.filler := by
  intro e
  cases d
  all_goals
    change ∀ mode, DiscardResult.label .unit e ≠ .focus mode
    intro mode
    rcases DiscardResult.fin_three e with rfl | rfl | rfl <;> intro eq <;> cases eq

/-- The original paired filling survives a write as a genuine pointed
specimen. The proof uses the common target-swapped original context, not a
new relation identifying the operands or their private boxes. -/
noncomputable def pointed {T : PreTemplate} {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    (left : Match (C.expand L) (Net.Expansion.host C L v))
    (right : Match (C.expand R) (Net.Expansion.host C R v))
    (l : LabelCopy (L m.headEdge) (C.edgeLabel m.headEdge))
    (r : LabelCopy (R m.headEdge) (C.edgeLabel m.headEdge))
    (leftHead : left.headEdge = ⟨m.headEdge,l.edge⟩)
    (rightHead : right.headEdge = ⟨m.headEdge,r.edge⟩)
    (leftNew : left.newValue = Net.Expansion.host C L m.newValue)
    (leftOld : left.oldValue = Net.Expansion.host C L m.oldValue)
    (rightNew : right.newValue = Net.Expansion.host C R m.newValue)
    (rightOld : right.oldValue = Net.Expansion.host C R m.oldValue) :
    BoxPullWeakening.PointedWitness T left.canonical.1 left.canonical.2.2
      right.canonical.1 right.canonical.2.2 := by
  let li := canonicalIso C m L left leftNew leftOld l leftHead
  let ri := canonicalIso C m R right rightNew rightOld r rightHead
  let w := RetainedReplacement.pointed m.swapped m.headEdge m.filler
    (TargetSwap.HostExpansion.certificate C m.newValue m.oldValue
      m.new_not_input m.old_not_input m.values_typed cert) free (filler_free C m) v
  have result := w.congr li.symm.graph ri.symm.graph
  simpa only [li.symm.vertex,ri.symm.vertex] using result

end Hypernets.Copying.Assignment.Retained

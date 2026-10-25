import Hypernets.Copying.SerialPlug
import Hypernets.Copying.CertifiedContextExamples
import Hypernets.Graph.PlugUnits

/-! Addressed filling through the literal unary clause of Figure 16. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph

/-- Follow an argument edge through the operation prefix and distributor suffix. -/
def unaryEdge {d k h} (o : Unary) (G : Hypernet d [.term] (environmentInterface k h))
    (e : G.Edge) : (unary o G).Edge :=
  Serial.leftEdge _ (singleUse d k h)
    (Serial.rightEdge (primitiveNet d (.operation (.unary o))) G e)

theorem unaryEdge_label {d k h} (o : Unary) (G : Hypernet d [.term] (environmentInterface k h))
    (e : G.Edge) : (unary o G).edgeLabel (unaryEdge o G e) = G.edgeLabel e :=
  (Serial.leftEdge_label ..).trans (Serial.rightEdge_label ..)

/-- Shallow replacement commutes with the unchanged unary translation clause. -/
noncomputable def unary_plug {d k h} (o : Unary)
    (G : Hypernet d [.term] (environmentInterface k h)) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) :
    DeepIso ((unary o G).plug (unaryEdge o G e)
      (A.reboundary (congrArg _ (unaryEdge_label o G e)).symm
        (congrArg _ (unaryEdge_label o G e)).symm)) (unary o (G.plug e A)) := by
  cases d with
  | zero =>
    let P := primitiveNet 0 (.operation (.unary o))
    have l := Serial.plug_left (Serial.net P G) (singleUse 0 k h) (Serial.rightEdge P G e) A
    have r := Serial.plug_right P G e A
    simp only [Net.reboundary_refl] at l r ⊢
    exact (DeepIso.ofIso l).trans
      (Serial.congr (DeepIso.ofIso r) (DeepIso.refl _))
  | succ d =>
    let P := primitiveNet (d+1) (.operation (.unary o))
    have l := Serial.plug_left (Serial.net P G) (singleUse (d+1) k h) (Serial.rightEdge P G e) A
    have r := Serial.plug_right P G e A
    simp only [Net.reboundary_refl] at l r ⊢
    exact (DeepIso.ofIso l).trans
      (Serial.congr (DeepIso.ofIso r) (DeepIso.refl _))

/-- Applying a unary operation to recursively isomorphic arguments preserves
recursive isomorphism, with all prescribed distributors still present. -/
def unary_congr {d k h} (o : Unary)
    {G H : Hypernet d [.term] (environmentInterface k h)} (f : DeepIso G H) :
    DeepIso (unary o G) (unary o H) :=
  Serial.congr (Serial.congr (DeepIso.refl _) f) (DeepIso.refl _)

/-- The actual shallow address of the annotated hole in a unary context. -/
def unaryHoleSite {k h} (o : Unary) (name : Nat) : (d : Nat) →
    Site (unary o (primitiveNet d (.hole ⟨name,[.term],environmentInterface k h⟩)))
      d [.term] (environmentInterface k h)
  | 0 => by exact .shallow _ (unaryEdge o (primitiveNet 0 (.hole ⟨name,[.term],environmentInterface k h⟩)) (by exact (0 : Fin 1)))
  | d+1 => by exact .shallow _ (unaryEdge o (primitiveNet (d+1) (.hole ⟨name,[.term],environmentInterface k h⟩)) (by exact (0 : Fin 1)))

/-- A specified outer hole in a single-hole inventory is the sole occurrence. -/
theorem sole_of_single_hole {d I O} (G : Hypernet d I O) (e : G.Edge) (q : Hole)
    (one : SingleHole q G) (label : G.edgeLabel e = primitiveLabel d (.hole q)) :
    SoleHole (Site.shallow G e) := by
  classical
  obtain ⟨f,_,others⟩ := one
  have eq : e = f := by
    by_cases ne : e = f
    · exact ne
    apply False.elim
    have free := others e ne
    rw [label] at free
    cases d <;> exact free q rfl
  subst f
  exact ⟨⟨q,label⟩,others⟩

/-- The address used by the filling theorem is itself a certified sole hole. -/
theorem unaryHoleSite_sole {k h} (o : Unary) (name d : Nat) :
    SoleHole (unaryHoleSite (k := k) (h := h) o name d) := by
  cases d with
  | zero =>
    apply sole_of_single_hole _ _ ⟨name,[.term],environmentInterface k h⟩
    · exact SingleHole.unary _ o (SingleHole.corolla _ _)
    · rw [unaryEdge_label]; rfl
  | succ d =>
    apply sole_of_single_hole _ _ ⟨name,[.term],environmentInterface k h⟩
    · exact SingleHole.unary _ o (SingleHole.corolla _ _)
    · rw [unaryEdge_label]; rfl

/-- Filling the actual translated unary context reconstructs the unary clause,
up to carrier isomorphism, for an arbitrary graph at its annotated interface. -/
noncomputable def unary_hole_filling {d k h} (o : Unary) (name : Nat)
    (G : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (plugAt (unaryHoleSite (k := k) (h := h) o name d) G) (unary o G) := by
  cases d with
  | zero =>
    have p := unary_plug o (primitiveNet 0 (.hole ⟨name,[.term],environmentInterface k h⟩)) (by exact (0 : Fin 1)) G
    simp only [Net.reboundary_refl] at p
    exact p.trans (unary_congr o (DeepIso.ofIso
      (Net.corolla_plug_iso (primitiveLabel 0 (.hole ⟨name,[.term],environmentInterface k h⟩)) G)))
  | succ d =>
    have p := unary_plug o (primitiveNet (d+1) (.hole ⟨name,[.term],environmentInterface k h⟩)) (by exact (0 : Fin 1)) G
    simp only [Net.reboundary_refl] at p
    exact p.trans (unary_congr o (DeepIso.ofIso
      (Net.corolla_plug_iso (primitiveLabel (d+1) (.hole ⟨name,[.term],environmentInterface k h⟩)) G)))

/-- The graph-filling law for a unary term context uses the original term
translator on both sides, not the constructor interpreter equality. -/
noncomputable def unary_term_filling {k h} (o : Unary) (name : Nat) (t : Term k h) :
    DeepIso (plugAt (unaryHoleSite (k := k) (h := h) o name (depth t)) (term t))
      (term (.unary o t)) := unary_hole_filling o name (term t)
end Hypernets.Copying.Translation

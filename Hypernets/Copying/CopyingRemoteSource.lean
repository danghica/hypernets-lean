import Hypernets.Copying.CopyingRemoteContext
import Hypernets.Copying.ContractionTreeGraftExpansion
import Hypernets.Copying.ContractionTreeGraftCongruence
import Hypernets.Copying.CommonContextLocalIso
import Hypernets.Copying.FillingWitness

/-! The computed original finite cut expands to the literal sharing prefix
and its actual entered filling. Retained sharing edges are collapsed using
proved labelled-corolla certificates; the selected hole keeps its entire
original recursively represented graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteContext
open Graph Opening ContractionTree
variable {d m b K} (P : ContractionTree .term (m+1)) (name : Nat) (j : Fin (b+1))

variable (U : Hypernet d (List.replicate (b+1) .term) K)

/-- Identity corollas on the original prefix and the full selected filling
at the one original hole. -/
def filledFamily (x : (Graft.net (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j).Edge) :
    Hypernet d ((alphabet d).signature.input
      ((Graft.net (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j).edgeLabel x))
      ((alphabet d).signature.output
      ((Graft.net (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j).edgeLabel x)) := by
  cases d <;> rcases x with ⟨side,x⟩ <;> cases side
  all_goals first | exact Net.corolla (alphabet _).signature ((P.atDepth _).edgeLabel x) | exact U

def holeFamily (x : (hole (d := d) (b := b) (K := K) name).Edge) :
    Hypernet d ((alphabet d).signature.input ((hole (d := d) (b := b) (K := K) name).edgeLabel x))
      ((alphabet d).signature.output ((hole (d := d) (b := b) (K := K) name).edgeLabel x)) := by
  cases d <;> exact U

/-- Filling the literal one-edge hole by its whole component restores that
component, with all ordered boundary coordinates fixed. -/
noncomputable def holeIso :
    DeepIso ((hole (d := d) (b := b) (K := K) name).expand (holeFamily name U)) U := by
  cases d with
  | zero =>
    let Z := hole (d := 0) (b := b) (K := K) name
    have same : holeFamily name U = SingleExpansion.family Z (0 : Fin 1) U := by
      funext x
      change Fin 1 at x
      have zero : x = (0 : Fin 1) := Subsingleton.elim _ _
      subst x
      simp only [SingleExpansion.selected]
      rfl
    rw [same]
    exact (SingleExpansion.iso Z (0 : Fin 1) U).trans
      (DeepIso.ofIso (Net.corolla_plug_iso (Z.edgeLabel (0 : Fin 1)) U))
  | succ d =>
    let Z := hole (d := d+1) (b := b) (K := K) name
    have same : holeFamily name U = SingleExpansion.family Z (0 : Fin 1) U := by
      funext x
      change Fin 1 at x
      have zero : x = (0 : Fin 1) := Subsingleton.elim _ _
      subst x
      simp only [SingleExpansion.selected]
      rfl
    rw [same]
    exact (SingleExpansion.iso Z (0 : Fin 1) U).trans
      (DeepIso.ofIso (Net.corolla_plug_iso (Z.edgeLabel (0 : Fin 1)) U))

/-- Actual graph reassociation exposes the original prefix and complete
selected graph, with no operational or copying law used. -/
noncomputable def filledIso :
    DeepIso
      ((Graft.net (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j).expand
        (filledFamily P name j U)) (Graft.net (P.atDepth d) U j) := by
  apply (Graft.expansionIso (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j
    (filledFamily P name j U)).trans
  apply Graft.congr
  · apply DeepIso.ofIso
    apply FillingCollapse.identity
    intro x
    cases d <;> exact LabelCopy.corolla _
  · have same : Graft.expansionRight (P.atDepth d) (hole (d := d) (b := b) (K := K) name) j
        (filledFamily P name j U) = holeFamily name U := by
      cases d <;> funext x <;> rfl
    rw [same]
    exact holeIso name U

variable {I O} (C : Hypernet d I O)
    (f : Occurrence (P.atDepth d) C) (e : C.Edge)
    (label : C.edgeLabel e = primitiveLabel d (.hole ⟨name,List.replicate (b+1) .term,K⟩))
    (link : f.ports (.output 0) = C.sourcePort e
      ⟨j.val,by rw [label,primitive_input]; simp [primitiveSignature]⟩)

variable (F : (x : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel x))
    ((alphabet d).signature.output (C.edgeLabel x)))
    (copies : ∀ x, LabelCopy (F (f.edges x)) ((P.atDepth d).edgeLabel x))
    (selected : DeepIso ((F e).reboundary
      (by rw [label,primitive_input]; rfl) (by rw [label,primitive_output]; rfl)) U)

/-- The actual original selected cut has precisely the stated literal graft
source. Every prefix certificate and the selected component's representation
is supplied explicitly by its original filling, not by a matching assumption. -/
noncomputable def sourceIso :
    DeepIso
      ((CommonContextCut.skeleton C (occurrence C P f e name label j link)).expand
        (CommonContextCut.localFamily C (occurrence C P f e name label j link) F))
      (Graft.net (P.atDepth d) U j) := by
  apply (CommonContextCut.localIso C (occurrence C P f e name label j link) F
    (filledFamily P name j U) ?_).trans (filledIso P name j U)
  intro x
  cases d
  all_goals
    rcases x with ⟨side,x⟩
    cases side
    · change DeepIso ((F (f.edges x)).reboundary _ _) (Net.corolla (alphabet _).signature ((P.atDepth _).edgeLabel x))
      exact ((copies x).reboundary _ _).iso (LabelCopy.corolla _) (labelEquiv_refl _ _)
    · change DeepIso ((F e).reboundary _ _) U
      exact selected

end Hypernets.Copying.CopyingTemplate.RemoteContext

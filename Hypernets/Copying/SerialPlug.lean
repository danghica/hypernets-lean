import Hypernets.Graph.ExpansionIso
import Hypernets.Graph.TransportPlug
import Hypernets.Graph.ExpansionPlug
import Hypernets.Copying.DeepComposition
import Hypernets.Copying.Serial

/-! Actual shallow replacement through the original serial graph constructor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial
open Graph

/-- The original occurrence of a left-component edge in serial assembly. -/
def leftEdge {I J K} : {d : Nat} → (G : Hypernet d I J) → (H : Hypernet d J K) → G.Edge →
    (net G H).Edge
  | 0, _, _, e => ⟨false,e⟩
  | _+1, _, _, e => ⟨false,e⟩

/-- The original occurrence of a right-component edge in serial assembly. -/
def rightEdge {I J K} : {d : Nat} → (G : Hypernet d I J) → (H : Hypernet d J K) → H.Edge →
    (net G H).Edge
  | 0, _, _, e => ⟨true,e⟩
  | _+1, _, _, e => ⟨true,e⟩

theorem leftEdge_label {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : G.Edge) :
    (net G H).edgeLabel (leftEdge G H e) = G.edgeLabel e := by cases d <;> rfl

theorem rightEdge_label {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : H.Edge) :
    (net G H).edgeLabel (rightEdge G H e) = H.edgeLabel e := by cases d <;> rfl

/-- Substitution into the left component commutes with serial assembly. -/
noncomputable def plug_left {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) :
    Net.Iso ((net G H).plug (leftEdge G H e)
      (A.reboundary (congrArg _ (leftEdge_label G H e)).symm
        (congrArg _ (leftEdge_label G H e)).symm)) (net (G.plug e A) H) := by
  classical
  cases d with
  | zero =>
    have eq : Net.ExpansionPlug.family (pattern 0 I J K) (filling G H) false e A =
        filling (G.plug e A) H := by
      funext b; cases b <;> simp [Net.ExpansionPlug.family,filling]
    simpa only [eq,Net.reboundary_refl,leftEdge,rightEdge] using Net.ExpansionPlug.iso (pattern 0 I J K) (filling G H) false e A
  | succ d =>
    have eq : Net.ExpansionPlug.family (pattern (d+1) I J K) (filling G H) false e A =
        filling (G.plug e A) H := by
      funext b; cases b <;> simp [Net.ExpansionPlug.family,filling]
    simpa only [eq,Net.reboundary_refl,leftEdge,rightEdge] using Net.ExpansionPlug.iso (pattern (d+1) I J K) (filling G H) false e A

/-- Substitution into the right component commutes with serial assembly. -/
noncomputable def plug_right {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (e : H.Edge)
    (A : Hypernet d ((alphabet d).signature.input (H.edgeLabel e))
      ((alphabet d).signature.output (H.edgeLabel e))) :
    Net.Iso ((net G H).plug (rightEdge G H e)
      (A.reboundary (congrArg _ (rightEdge_label G H e)).symm
        (congrArg _ (rightEdge_label G H e)).symm)) (net G (H.plug e A)) := by
  classical
  cases d with
  | zero =>
    have eq : Net.ExpansionPlug.family (pattern 0 I J K) (filling G H) true e A =
        filling G (H.plug e A) := by
      funext b; cases b <;> simp [Net.ExpansionPlug.family,filling]
    simpa only [eq,Net.reboundary_refl,leftEdge,rightEdge] using Net.ExpansionPlug.iso (pattern 0 I J K) (filling G H) true e A
  | succ d =>
    have eq : Net.ExpansionPlug.family (pattern (d+1) I J K) (filling G H) true e A =
        filling G (H.plug e A) := by
      funext b; cases b <;> simp [Net.ExpansionPlug.family,filling]
    simpa only [eq,Net.reboundary_refl,leftEdge,rightEdge] using Net.ExpansionPlug.iso (pattern (d+1) I J K) (filling G H) true e A
/-- Recursive isomorphisms of both components preserve the literal serial graph. -/
def congr {d I J K} {G G' : Hypernet d I J} {H H' : Hypernet d J K}
    (f : DeepIso G G') (g : DeepIso H H') : DeepIso (net G H) (net G' H') := by
  cases d with
  | zero => exact Net.ExpansionIso.iso (pattern 0 I J K) (fun b => match b with | false => f | true => g)
  | succ d => exact Net.ExpansionIso.iso (pattern (d+1) I J K) (fun b => match b with | false => f | true => g)
end Hypernets.Copying.Serial

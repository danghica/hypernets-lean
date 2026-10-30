import Hypernets.Copying.CommonContextCut
import Hypernets.Graph.ExpansionTransport

/-! Local normalized common cuts compare to literal program-rule frames by
componentwise recursive isomorphisms, preserving the actual frame token. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CommonContextCut
open Graph
variable {d I O} (C : Hypernet d I O) {J K} {A : Hypernet d J K}
    (f : Opening.Occurrence A C)

/-- Normalizing source labels changes no carriers or incidence; original
full-label matching supplies the recursive label comparison back to A. -/
def skeletonIso : DeepIso (skeleton C f) A where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label e := labelEquiv_symm _ (f.label e)
  source e := by change (A.source e).map (Port.map id) = _; rw [List.map_id'' (fun v => by cases v <;> rfl)]; rfl
  target e := by change (A.target e).map (Port.map id) = _; rw [List.map_id'' (fun v => by cases v <;> rfl)]; rfl

variable (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (D : (e : A.Edge) → Hypernet d ((alphabet d).signature.input (A.edgeLabel e))
      ((alphabet d).signature.output (A.edgeLabel e)))
    (components : ∀ e, DeepIso ((F (f.edges e)).reboundary
      (labelEquiv_input d (f.label e)).symm (labelEquiv_output d (f.label e)).symm) (D e))

/-- Compare the exact original selected fillings to any established local
frame components, without changing the outer ordered boundary. -/
noncomputable def localIso : DeepIso ((skeleton C f).expand (localFamily C f F)) (A.expand D) :=
  Net.ExpansionTransport.iso (skeletonIso C f)
    (fun e => (labelEquiv_input d (f.label e)).symm)
    (fun e => (labelEquiv_output d (f.label e)).symm)
    (localFamily C f F) D components

theorem localIso_host (v : A.Vertex) :
    Port.map (localIso C f F D components).vertices.toFun
      (Net.Expansion.host (skeleton C f) (localFamily C f F) v) =
      Net.Expansion.host A D v := by cases v <;> rfl

end Hypernets.Copying.CommonContextCut

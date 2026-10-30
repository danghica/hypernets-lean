import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.FillingTransport
import Hypernets.Graph.PlugUnits

/-! Literal edge corollas embed into their actual original host with ordered
source and target attachments, including primitive interface casts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph
variable {d I O} (C : Hypernet d I O) (e : C.Edge)

def corollaPorts : (Net.corolla (alphabet d).signature (C.edgeLabel e)).Vertex → C.Vertex
  | .input i => C.sourcePort e i
  | .output i => C.targetPort e i
  | .internal x => nomatch x

/-- The finite corolla of any original edge has a complete original match. -/
noncomputable def corolla : Occurrence (Net.corolla (alphabet d).signature (C.edgeLabel e)) C :=
  (show MatchEmbedding (Net.corolla (alphabet d).signature (C.edgeLabel e)) C from {
    ports := corollaPorts C e
    edges := fun _ => e
    edge_injective := by intro a b _; exact Subsingleton.elim _ _
    primitive := fun _ _ label => label
    source := by
      intro j
      change ((List.finRange _).map Port.input).map _ = _
      rw [List.map_map]
      exact Net.PlugUnit.sourcePort_list C e
    target := by
      intro j
      change ((List.finRange _).map Port.output).map _ = _
      rw [List.map_map]
      exact Net.PlugUnit.targetPort_list C e
  }).occurrence (fun _ => labelEquiv_refl _ _)

/-- A literal equality of edge labels retypes its canonical corolla. -/
noncomputable def labelledCorolla (a : (alphabet d).Symbol) (label : C.edgeLabel e = a) :
    Occurrence (Net.corolla (alphabet d).signature a) C := label ▸ corolla C e

theorem labelledCorolla_input (a : (alphabet d).Symbol) (label : C.edgeLabel e = a)
    (i : Fin ((alphabet d).signature.input a).length) :
    (labelledCorolla C e a label).ports (.input i) = C.sourcePort e
      (Fin.cast (congrArg (fun a => ((alphabet d).signature.input a).length) label).symm i) := by
  cases label; rfl

theorem labelledCorolla_output (a : (alphabet d).Symbol) (label : C.edgeLabel e = a)
    (i : Fin ((alphabet d).signature.output a).length) :
    (labelledCorolla C e a label).ports (.output i) = C.targetPort e
      (Fin.cast (congrArg (fun a => ((alphabet d).signature.output a).length) label).symm i) := by
  cases label; rfl

theorem labelledCorolla_edges (a : (alphabet d).Symbol) (label : C.edgeLabel e = a) (i : Fin 1) :
    (labelledCorolla C e a label).edges i = e := by cases label; rfl

/-- Reindexing the selected local boundary does not change its host graph. -/
def reboundarySource {J K P Q} {G : Hypernet d J K} {H : Hypernet d P Q}
    (f : Occurrence G H) {J' K'} (hi : J = J') (ho : K = K') :
    Occurrence (G.reboundary hi ho) H where
  ports v := f.ports (Port.cast hi.symm ho.symm v)
  internals := f.internals
  edges := f.edges
  internal_map x := f.internal_map x
  internal_injective := f.internal_injective
  edge_injective := f.edge_injective
  internal_label := f.internal_label
  label := f.label
  source e := by
    change ((G.source e).map (Port.cast hi ho)).map _ = _
    rw [List.map_map,← f.source]
    apply List.map_congr_left
    intro v _
    cases hi; cases ho; cases v <;> rfl
  target e := by
    change ((G.target e).map (Port.cast hi ho)).map _ = _
    rw [List.map_map,← f.target]
    apply List.map_congr_left
    intro v _
    cases hi; cases ho; cases v <;> rfl

theorem reboundarySource_ports {J K P Q} {G : Hypernet d J K} {H : Hypernet d P Q}
    (f : Occurrence G H) {J' K'} (hi : J = J') (ho : K = K') (v : G.Vertex) :
    (f.reboundarySource hi ho).ports (Port.cast hi ho v) = f.ports v := by
  cases hi; cases ho; cases v <;> rfl

/-- Every primitive net is the canonical complete corolla of its label. -/
def primitiveCopy (d : Nat) (p : Primitive) : LabelCopy (primitiveNet d p) (primitiveLabel d p) := by
  cases d <;> exact LabelCopy.corolla _

/-- A primitive edge in the original context gives a canonical primitive-net
occurrence, with all interface casts justified by its actual label equality. -/
noncomputable def primitive {p : Primitive} (label : C.edgeLabel e = primitiveLabel d p) :
    Occurrence (primitiveNet d p) C :=
  (Occurrence.ofIso ((primitiveCopy d p).iso
    ((LabelCopy.corolla (C.edgeLabel e)).reboundary
      ((congrArg ((alphabet d).signature.input) label).trans (primitive_input d p))
      ((congrArg ((alphabet d).signature.output) label).trans (primitive_output d p)))
    (by rw [label]; exact labelEquiv_refl _ _))).comp
    ((corolla C e).reboundarySource
      ((congrArg ((alphabet d).signature.input) label).trans (primitive_input d p))
      ((congrArg ((alphabet d).signature.output) label).trans (primitive_output d p)))

theorem primitive_input {p : Primitive} (label : C.edgeLabel e = primitiveLabel d p)
    (i : Fin (primitiveSignature.input p).length) :
    (primitive C e label).ports (.input i) = C.sourcePort e
      ⟨i.val,by rw [label,Copying.primitive_input]; exact i.isLt⟩ := rfl

theorem primitive_output {p : Primitive} (label : C.edgeLabel e = primitiveLabel d p)
    (i : Fin (primitiveSignature.output p).length) :
    (primitive C e label).ports (.output i) = C.targetPort e
      ⟨i.val,by rw [label,Copying.primitive_output]; exact i.isLt⟩ := rfl

end Hypernets.Copying.Opening.Occurrence

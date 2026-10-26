import Hypernets.Copying.CombinedTyping

/-! Padding of shallow matches, including their actual token coordinates.
These are graph representation lemmas, not changes to the transition relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Padding
open Graph

/-- A filled edge's interface is unchanged by padding, with explicit equality casts. -/
def expandFilling {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge) :=
  (graph (F e)).reboundary (label_input d (C.edgeLabel e)).symm
    (label_output d (C.edgeLabel e)).symm

/-- The input and output casts do not move the attachment in the padded host. -/
theorem expand_insert {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge) (v : (F e).Vertex) :
    Net.Expansion.insert (graph C) (expandFilling C F) e
      (Port.cast (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm v) =
    Net.Expansion.insert C F e v := by
  cases v <;> simp [expandFilling,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,
    graph,Net.relabel,Port.cast]

/-- Simultaneous assembly commutes with padding on the actual finite carriers. -/
noncomputable def expand_graph {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) :
    Net.Iso (graph (C.expand F)) ((graph C).expand (expandFilling C F)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := rfl
  source e := by
    simp only [graph,Net.relabel,Net.expand,Net.Expansion.source,expandFilling,Net.reboundary,
      Bijection.refl,Port.map_id_fun,List.map_map]
    apply List.map_congr_left
    intro v _
    exact (expand_insert C F e.1 v).symm
  target e := by
    simp only [graph,Net.relabel,Net.expand,Net.Expansion.target,expandFilling,Net.reboundary,
      Bijection.refl,Port.map_id_fun,List.map_map]
    apply List.map_congr_left
    intro v _
    exact (expand_insert C F e.1 v).symm

/-- The same attachment equation for a single selected slot. -/
theorem plug_insert {d I O} (C : Hypernet d I O) (e : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (v : G.Vertex) :
    Net.Replacement.insert (graph C) e
      ((graph G).reboundary (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm)
      (Port.cast (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm v) =
    Net.Replacement.insert C e G v := by
  cases v <;> simp [Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,Net.targetPort,
    graph,Net.relabel,Port.cast]
/-- Single-slot assembly commutes with padding without a cast on the original filler. -/
noncomputable def plug_graph {d I O} (C : Hypernet d I O) (e : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) :
    Net.Iso (graph (C.plug e G)) ((graph C).plug e
      ((graph G).reboundary (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := by cases e <;> rfl
  source x := by
    cases x with
    | inl x => simp [graph,Net.relabel,Bijection.refl,Net.Replacement.source,Net.Replacement.host]
    | inr x =>
      simp only [graph,Net.relabel,Net.plug,Net.Replacement.source,Net.reboundary,
        Bijection.refl,Port.map_id_fun,List.map_map]
      apply List.map_congr_left
      intro v _
      exact (plug_insert C e G v).symm
  target x := by
    cases x with
    | inl x => simp [graph,Net.relabel,Bijection.refl,Net.Replacement.target,Net.Replacement.host]
    | inr x =>
      simp only [graph,Net.relabel,Net.plug,Net.Replacement.target,Net.reboundary,
        Bijection.refl,Port.map_id_fun,List.map_map]
      apply List.map_congr_left
      intro v _
      exact (plug_insert C e G v).symm

/-- Intrinsic search transports through the uniform padding presentation. -/
def search {d I O} (G : Hypernet d I O) : Search.Transport G (graph G) where
  ports := Bijection.refl _
  edges := Bijection.refl _
  primitive e p := by
    cases d with
    | zero => cases eq : G.edgeLabel e; simp [graph,Net.relabel,label,primitiveLabel,Bijection.refl,eq] <;> constructor <;> intro h <;> cases h <;> rfl
    | succ d => cases eq : G.edgeLabel e <;> simp [graph,Net.relabel,label,primitiveLabel,Bijection.refl,eq] <;> constructor <;> intro h <;> cases h <;> rfl
  source e := by simp [graph,Net.relabel,Bijection.refl]
  target e := by simp [graph,Net.relabel,Bijection.refl]
  input_iff v := Iff.rfl
end Hypernets.Copying.Padding

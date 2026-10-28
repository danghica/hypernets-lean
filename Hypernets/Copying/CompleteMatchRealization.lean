import Hypernets.Copying.CompleteMatchCut
import Hypernets.Graph.ComplementBijection

/-! A complete occurrence is literally the filling of its constructed finite
complement, up to recursive graph representation. Boundary input/output aliases
are retained by the hole attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)

def internalComplement : Bijection (Internal f)
    {v : G.Internal // ∀ a, f.internal a ≠ v} where
  toFun v := ⟨v.val, fun a eq => v.property a
    ((f.ports_internal a).trans (congrArg Port.internal eq))⟩
  invFun v := ⟨v.val, fun a eq => v.property a
    (Port.internal.inj ((f.ports_internal a).symm.trans eq))⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The internal carriers of the complement and matched graph reconstruct
exactly the original host internal carrier. -/
noncomputable def vertices : Bijection (Internal f ⊕ A.Internal) G.Internal :=
  (Bijection.sum (internalComplement f) (Bijection.refl _)).trans
    (Bijection.ofComplement f.internal f.internal_injective)

@[simp] theorem vertices_left (v : Internal f) : (vertices f).toFun (.inl v) = v.val := rfl
@[simp] theorem vertices_right (v : A.Internal) :
    (vertices f).toFun (.inr v) = f.internal v := rfl

/-- Removing the fresh hole leaves exactly the retained original edges. -/
def retainedEdges : Bijection {e : Option (RetainedEdge f) // e ≠ none} (RetainedEdge f) where
  toFun e := match e with
    | ⟨none, h⟩ => False.elim (h rfl)
    | ⟨some e, _⟩ => e
  invFun e := ⟨some e, Option.some_ne_none e⟩
  left_inv e := by rcases e with ⟨e,h⟩; cases e with
    | none => exact False.elim (h rfl)
    | some e => rfl
  right_inv _ := rfl

/-- All retained and matched edge occurrences reconstruct the original edges. -/
noncomputable def edges : Bijection
    ({e : Option (RetainedEdge f) // e ≠ none} ⊕ A.Edge) G.Edge :=
  (Bijection.sum (retainedEdges f) (Bijection.refl _)).trans
    (Bijection.ofComplement f.edges f.edge_injective)

@[simp] theorem edges_left (e : RetainedEdge f) :
    (edges f).toFun (.inl ⟨some e, Option.some_ne_none e⟩) = e.val := rfl
@[simp] theorem edges_right (e : A.Edge) : (edges f).toFun (.inr e) = f.edges e := rfl

variable (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

theorem hole_input : (alphabet d).signature.input ((net f labels).edgeLabel none) = J := by
  simp [net,label,primitive_input,primitiveSignature]

theorem hole_output : (alphabet d).signature.output ((net f labels).edgeLabel none) = K := by
  simp [net,label,primitive_output,primitiveSignature]

/-- Only the proof of the hole's interface is changed; every carrier and
operation of the matched graph is preserved. -/
noncomputable def replacement := A.reboundary (hole_input f labels).symm (hole_output f labels).symm

theorem map_host (v : (net f labels).Vertex) :
    Port.map (vertices f).toFun (Net.Replacement.host (net f labels) none (replacement f labels) v) =
      embed f v := by
  cases v <;> rfl

theorem hole_sourcePort (i : Fin J.length) :
    (net f labels).sourcePort none (Fin.cast (congrArg List.length (hole_input f labels).symm) i) =
      inputPort f i := by
  simp [Net.sourcePort,net,source,List.getElem_map]

theorem hole_targetPort (i : Fin K.length) :
    (net f labels).targetPort none (Fin.cast (congrArg List.length (hole_output f labels).symm) i) =
      outputPort f i := by
  simp [Net.targetPort,net,target,List.getElem_map]

/-- The plug insertion, followed by reconstruction, is the original occurrence
on every port, including boundary ports identified by the host. -/
theorem map_insert (v : A.Vertex) :
    Port.map (vertices f).toFun
      (Net.Replacement.insert (net f labels) none (replacement f labels)
        (Port.cast (hole_input f labels).symm (hole_output f labels).symm v)) = f.ports v := by
  cases v with
  | internal a => exact (f.ports_internal a).symm
  | input i =>
    change Port.map (vertices f).toFun (Net.Replacement.host (net f labels) none (replacement f labels)
      ((net f labels).sourcePort none _)) = _
    rw [map_host f labels]
    exact (congrArg (embed f) (hole_sourcePort f labels i)).trans (embed_input f i)
  | output i =>
    change Port.map (vertices f).toFun (Net.Replacement.host (net f labels) none (replacement f labels)
      ((net f labels).targetPort none _)) = _
    rw [map_host f labels]
    exact (congrArg (embed f) (hole_targetPort f labels i)).trans (embed_output f i)

/-- Cutting out a complete match and filling its hole reconstructs the entire
host, with its original ordered boundary and recursive labels. -/
noncomputable def realization :
    DeepIso ((net f labels).plug none (replacement f labels)) G where
  vertices := vertices f
  edges := edges f
  internal_label v := by
    cases v with
    | inl v => rfl
    | inr v =>
      have h := f.vertexLabel labels (.internal v)
      rw [f.ports_internal] at h
      exact h
  edge_label e := by
    cases e with
    | inl e =>
      rcases e with ⟨e,h⟩
      cases e with
      | none => exact False.elim (h rfl)
      | some e => exact labelEquiv_refl d _
    | inr e => exact labels e
  source e := by
    cases e with
    | inl e =>
      rcases e with ⟨e,h⟩
      cases e with
      | none => exact False.elim (h rfl)
      | some e =>
        change ((retainedSource f e).map _).map _ = G.source e.val
        rw [List.map_map]
        simp only [Function.comp_def,map_host f labels]
        exact embed_retainedSource f e
    | inr e =>
      change ((((A.source e).map _).map _).map _) = G.source (f.edges e)
      rw [List.map_map,List.map_map]
      simp only [Function.comp_def,map_insert f labels]
      exact f.source e
  target e := by
    cases e with
    | inl e =>
      rcases e with ⟨e,h⟩
      cases e with
      | none => exact False.elim (h rfl)
      | some e =>
        change ((retainedTarget f e).map _).map _ = G.target e.val
        rw [List.map_map]
        simp only [Function.comp_def,map_host f labels]
        exact embed_retainedTarget f e
    | inr e =>
      change ((((A.target e).map _).map _).map _) = G.target (f.edges e)
      rw [List.map_map,List.map_map]
      simp only [Function.comp_def,map_insert f labels]
      exact f.target e

end Hypernets.Copying.CompleteMatchCut

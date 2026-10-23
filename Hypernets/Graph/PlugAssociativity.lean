import Hypernets.Graph.Isomorphism

/-! Associativity of nested shallow replacement, including self-loop interfaces. -/
namespace Hypernets.Graph.Net
universe u
namespace PlugAssoc
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O) (e : C.Edge)
    (H : Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e))) (f : H.Edge)
    (K : Net σ (σ.input (H.edgeLabel f)) (σ.output (H.edgeLabel f)))

/-- Reassociate the three disjoint internal-vertex carriers. -/
def vertices : Bijection ((C.Internal ⊕ H.Internal) ⊕ K.Internal)
    (C.Internal ⊕ (H.Internal ⊕ K.Internal)) where
  toFun | .inl (.inl x) => .inl x | .inl (.inr y) => .inr (.inl y) | .inr z => .inr (.inr z)
  invFun | .inl x => .inl (.inl x) | .inr (.inl y) => .inl (.inr y) | .inr (.inr z) => .inr z
  left_inv x := by rcases x with (x | y) | z <;> rfl
  right_inv x := by rcases x with x | (y | z) <;> rfl

/-- Reassociate surviving host, surviving middle, and final replacement edges. -/
def edges : Bijection (Replacement.Edge (C.plug e H) (.inr f) K)
    (Replacement.Edge C e (H.plug f K)) where
  toFun
    | .inl ⟨.inl x, _⟩ => .inl x
    | .inl ⟨.inr y, hy⟩ => .inr (.inl ⟨y, fun eq => hy (congrArg Sum.inr eq)⟩)
    | .inr z => .inr (.inr z)
  invFun
    | .inl x => .inl ⟨.inl x, by intro h; cases h⟩
    | .inr (.inl y) => .inl ⟨.inr y.val, fun eq => y.property (Sum.inr.inj eq)⟩
    | .inr (.inr z) => .inr z
  left_inv x := by rcases x with ⟨x | y, h⟩ | z <;> rfl
  right_inv x := by rcases x with x | (y | z) <;> rfl

/-- The selected inserted edge has the mapped source attachment list. -/
theorem sourcePort_inserted (i) :
    (C.plug e H).sourcePort (.inr f) i = Replacement.insert C e H (H.sourcePort f i) := by
  simp [sourcePort, plug, Replacement.source, List.getElem_map]

/-- The selected inserted edge has the mapped target attachment list. -/
theorem targetPort_inserted (i) :
    (C.plug e H).targetPort (.inr f) i = Replacement.insert C e H (H.targetPort f i) := by
  simp [targetPort, plug, Replacement.target, List.getElem_map]

/-- Host inclusion is independent of the bracketing of replacement. -/
theorem map_host (v : C.Vertex) :
    Port.map (vertices C e H f K).toFun
      (Replacement.host (C.plug e H) (.inr f) K (Replacement.host C e H v)) =
      Replacement.host C e (H.plug f K) v := by cases v <;> rfl

/-- Middle-graph ports commute with reassociation and the two inclusions. -/
theorem map_middle (v : H.Vertex) :
    Port.map (vertices C e H f K).toFun
      (Replacement.host (C.plug e H) (.inr f) K (Replacement.insert C e H v)) =
      Replacement.insert C e (H.plug f K) (Replacement.host H f K v) := by
  cases v with
  | internal v => rfl
  | input i => exact map_host C e H f K _
  | output i => exact map_host C e H f K _

/-- Final replacement ports commute with reassociation and composed insertion. -/
theorem map_insert (v : K.Vertex) :
    Port.map (vertices C e H f K).toFun (Replacement.insert (C.plug e H) (.inr f) K v) =
      Replacement.insert C e (H.plug f K) (Replacement.insert H f K v) := by
  cases v with
  | internal v => rfl
  | input i =>
      change Port.map (vertices C e H f K).toFun (Replacement.host (C.plug e H) (.inr f) K ((C.plug e H).sourcePort (.inr f) i)) = _
      exact (congrArg (fun v => Port.map (vertices C e H f K).toFun
        (Replacement.host (C.plug e H) (.inr f) K v))
        (sourcePort_inserted C e H f i)).trans (map_middle C e H f K _)
  | output i =>
      change Port.map (vertices C e H f K).toFun (Replacement.host (C.plug e H) (.inr f) K ((C.plug e H).targetPort (.inr f) i)) = _
      exact (congrArg (fun v => Port.map (vertices C e H f K).toFun
        (Replacement.host (C.plug e H) (.inr f) K v))
        (targetPort_inserted C e H f i)).trans (map_middle C e H f K _)
end PlugAssoc

/-- Substituting inside an inserted graph agrees, up to explicit carrier
isomorphism, with performing that substitution before insertion. -/
noncomputable def plug_assoc {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O) (e : C.Edge)
    (H : Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e))) (f : H.Edge)
    (K : Net σ (σ.input (H.edgeLabel f)) (σ.output (H.edgeLabel f))) :
    Iso ((C.plug e H).plug (.inr f) K) (C.plug e (H.plug f K)) where
  vertices := PlugAssoc.vertices C e H f K
  edges := PlugAssoc.edges C e H f K
  internal_label x := by rcases x with (x | y) | z <;> rfl
  edge_label x := by rcases x with ⟨x | y, h⟩ | z <;> rfl
  source x := by
    rcases x with ⟨x | y, h⟩ | z
    · change (((C.source x.val).map _).map _).map _ = _
      simp only [plug, Replacement.source, PlugAssoc.edges, Net.Vertex, Replacement.Vertex, Replacement.edgeLabel, List.map_map]
      exact List.map_congr_left (fun v _ => PlugAssoc.map_host C e H f K v)
    · change (((H.source y).map _).map _).map _ = _
      simp only [plug, Replacement.source, PlugAssoc.edges, Net.Vertex, Replacement.Vertex, Replacement.edgeLabel, List.map_map]
      exact List.map_congr_left (fun v _ => PlugAssoc.map_middle C e H f K v)
    · change ((K.source z).map (Replacement.insert (C.plug e H) (.inr f) K)).map
        (Port.map (PlugAssoc.vertices C e H f K).toFun) =
        ((K.source z).map (Replacement.insert H f K)).map (Replacement.insert C e (H.plug f K))
      exact (List.map_map ..).trans
        ((List.map_congr_left (fun v _ => PlugAssoc.map_insert C e H f K v)).trans
          (List.map_map (f := Replacement.insert H f K)
            (g := Replacement.insert C e (H.plug f K))).symm)
  target x := by
    rcases x with ⟨x | y, h⟩ | z
    · change (((C.target x.val).map _).map _).map _ = _
      simp only [plug, Replacement.target, PlugAssoc.edges, Net.Vertex, Replacement.Vertex, Replacement.edgeLabel, List.map_map]
      exact List.map_congr_left (fun v _ => PlugAssoc.map_host C e H f K v)
    · change (((H.target y).map _).map _).map _ = _
      simp only [plug, Replacement.target, PlugAssoc.edges, Net.Vertex, Replacement.Vertex, Replacement.edgeLabel, List.map_map]
      exact List.map_congr_left (fun v _ => PlugAssoc.map_middle C e H f K v)
    · change ((K.target z).map (Replacement.insert (C.plug e H) (.inr f) K)).map
        (Port.map (PlugAssoc.vertices C e H f K).toFun) =
        ((K.target z).map (Replacement.insert H f K)).map (Replacement.insert C e (H.plug f K))
      exact (List.map_map ..).trans
        ((List.map_congr_left (fun v _ => PlugAssoc.map_insert C e H f K v)).trans
          (List.map_map (f := Replacement.insert H f K)
            (g := Replacement.insert C e (H.plug f K))).symm)

end Hypernets.Graph.Net

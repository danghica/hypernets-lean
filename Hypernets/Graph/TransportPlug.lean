import Hypernets.Graph.RelIsoPlug

/-! Transporting interfaces and host names through shallow replacement. -/
namespace Hypernets.Graph
universe u

/-- Reindex boundary positions along equal ordered interfaces. -/
def Port.cast {V : Type} {I O I' O' : List L} (hi : I = I') (ho : O = O') :
    Port V I.length O.length → Port V I'.length O'.length
  | .internal v => .internal v
  | .input i => .input ⟨i.val, by simp [← hi]⟩
  | .output i => .output ⟨i.val, by simp [← ho]⟩

@[simp] theorem Port.cast_refl {V : Type} {I O : List L} (v : Port V I.length O.length) :
    Port.cast (I := I) (O := O) rfl rfl v = v := by cases v <;> rfl

@[simp] theorem Port.cast_refl_fun {V : Type} {I O : List L} :
    Port.cast (V := V) (I := I) (O := O) rfl rfl = id := by
  funext v; exact Port.cast_refl v

/-- Interface transport keeps the actual internal and edge carriers unchanged. -/
def Net.reboundary {L : Type} {Op : Type u} {σ : Signature L Op}
    {I O I' O' : List L} (G : Net σ I O) (hi : I = I') (ho : O = O') : Net σ I' O' where
  Internal := G.Internal
  Edge := G.Edge
  finiteInternal := G.finiteInternal
  finiteEdge := G.finiteEdge
  internalLabel := G.internalLabel
  edgeLabel := G.edgeLabel
  source e := (G.source e).map (Port.cast hi ho)
  target e := (G.target e).map (Port.cast hi ho)
  source_nodup := by cases hi; cases ho; simpa using G.source_nodup
  target_nodup := by cases hi; cases ho; simpa using G.target_nodup
  source_unique := by cases hi; cases ho; simpa using @G.source_unique
  target_unique := by cases hi; cases ho; simpa using @G.target_unique
  source_coverage := by cases hi; cases ho; simpa using G.source_coverage
  target_coverage := by cases hi; cases ho; simpa using G.target_coverage
  source_typed := by cases hi; cases ho; simpa using G.source_typed
  target_typed := by cases hi; cases ho; simpa using G.target_typed

@[simp] theorem Net.reboundary_refl {L : Type} {Op : Type u} {σ : Signature L Op}
    {I O : List L} (G : Net σ I O) : G.reboundary rfl rfl = G := by
  cases G; simp [Net.reboundary]

/-- Restrict a bijection to the complements of corresponding selected elements. -/
def Bijection.except {α β : Type} (f : Bijection α β) (a : α) :
    Bijection {x : α // x ≠ a} {y : β // y ≠ f.toFun a} where
  toFun x := ⟨f.toFun x.val, fun h => x.property (f.injective h)⟩
  invFun y := ⟨f.invFun y.val, fun h => y.property (by rw [← f.right_inv y.val, h])⟩
  left_inv x := Subtype.ext (f.left_inv x.val)
  right_inv y := Subtype.ext (f.right_inv y.val)

namespace Net
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R : Op → Op → Prop} {C D : Net σ I O}

/-- Ordered source positions are carried to the corresponding host positions. -/
theorem RelIso.sourcePort (f : RelIso R C D) (e : C.Edge)
    (hi : σ.input (C.edgeLabel e) = σ.input (D.edgeLabel (f.edges.toFun e)))
    (i : Fin (σ.input (C.edgeLabel e)).length) :
    Port.map f.vertices.toFun (C.sourcePort e i) =
      D.sourcePort (f.edges.toFun e) ⟨i.val, by simp [← hi]⟩ := by
  have h := congrArg (fun xs => xs[i.val]?) (f.source e)
  simpa [List.getElem?_eq_getElem, List.getElem_map, Net.sourcePort,
    C.source_length, D.source_length, ← hi, i.isLt] using h

/-- Ordered target positions are carried to the corresponding host positions. -/
theorem RelIso.targetPort (f : RelIso R C D) (e : C.Edge)
    (ho : σ.output (C.edgeLabel e) = σ.output (D.edgeLabel (f.edges.toFun e)))
    (i : Fin (σ.output (C.edgeLabel e)).length) :
    Port.map f.vertices.toFun (C.targetPort e i) =
      D.targetPort (f.edges.toFun e) ⟨i.val, by simp [← ho]⟩ := by
  have h := congrArg (fun xs => xs[i.val]?) (f.target e)
  simpa [List.getElem?_eq_getElem, List.getElem_map, Net.targetPort,
    C.target_length, D.target_length, ← ho, i.isLt] using h

namespace HostPlug
variable (f : RelIso R C D) (e : C.Edge)
    (hi : σ.input (C.edgeLabel e) = σ.input (D.edgeLabel (f.edges.toFun e)))
    (ho : σ.output (C.edgeLabel e) = σ.output (D.edgeLabel (f.edges.toFun e)))
    (H : Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))

def vertices : Bijection (C.Internal ⊕ H.Internal) (D.Internal ⊕ H.Internal) :=
  f.vertices.sum (Bijection.refl _)

def edges : Bijection (Replacement.Edge C e H)
    (Replacement.Edge D (f.edges.toFun e) (H.reboundary hi ho)) :=
  (f.edges.except e).sum (Bijection.refl _)

theorem map_host (v : C.Vertex) :
    Port.map (vertices f e H).toFun (Replacement.host C e H v) =
      Replacement.host D (f.edges.toFun e) (H.reboundary hi ho)
        (Port.map f.vertices.toFun v) := by cases v <;> rfl

theorem map_insert (v : H.Vertex) :
    Port.map (vertices f e H).toFun (Replacement.insert C e H v) =
      Replacement.insert D (f.edges.toFun e) (H.reboundary hi ho) (Port.cast hi ho v) := by
  cases v with
  | internal v => rfl
  | input i =>
      change Port.map (vertices f e H).toFun (Replacement.host C e H (C.sourcePort e i)) = _
      rw [map_host f e hi ho H, f.sourcePort e hi i]
      rfl
  | output i =>
      change Port.map (vertices f e H).toFun (Replacement.host C e H (C.targetPort e i)) = _
      rw [map_host f e hi ho H, f.targetPort e ho i]
      rfl
end HostPlug

/-- Renaming a host carries the selected edge and all its attachment positions;
replacement is transported along the equal selected interfaces. -/
def RelIso.plugHost (f : RelIso R C D) (e : C.Edge)
    (hi : σ.input (C.edgeLabel e) = σ.input (D.edgeLabel (f.edges.toFun e)))
    (ho : σ.output (C.edgeLabel e) = σ.output (D.edgeLabel (f.edges.toFun e)))
    (reflexive : ∀ a, R a a)
    (H : Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e))) :
    RelIso R (C.plug e H) (D.plug (f.edges.toFun e) (H.reboundary hi ho)) where
  vertices := HostPlug.vertices f e H
  edges := HostPlug.edges f e hi ho H
  internal_label v := by
    cases v with
    | inl v => exact f.internal_label v
    | inr v => rfl
  edge_label x := by
    cases x with
    | inl x => exact f.edge_label x.val
    | inr x => exact reflexive _
  source x := by
    cases x with
    | inl x =>
        change ((C.source x.val).map (Replacement.host C e H)).map
          (Port.map (HostPlug.vertices f e H).toFun) =
          (D.source (f.edges.toFun x.val)).map
            (Replacement.host D (f.edges.toFun e) (H.reboundary hi ho))
        rw [← f.source]
        simp only [List.map_map]
        congr 1; funext v; exact HostPlug.map_host f e hi ho H v
    | inr x =>
        change ((H.source x).map (Replacement.insert C e H)).map
          (Port.map (HostPlug.vertices f e H).toFun) =
          ((H.source x).map (Port.cast hi ho)).map
            (Replacement.insert D (f.edges.toFun e) (H.reboundary hi ho))
        simp only [Net.Vertex, Net.reboundary, List.map_map]
        exact List.map_congr_left (fun v _ => HostPlug.map_insert f e hi ho H v)
  target x := by
    cases x with
    | inl x =>
        change ((C.target x.val).map (Replacement.host C e H)).map
          (Port.map (HostPlug.vertices f e H).toFun) =
          (D.target (f.edges.toFun x.val)).map
            (Replacement.host D (f.edges.toFun e) (H.reboundary hi ho))
        rw [← f.target]
        simp only [List.map_map]
        congr 1; funext v; exact HostPlug.map_host f e hi ho H v
    | inr x =>
        change ((H.target x).map (Replacement.insert C e H)).map
          (Port.map (HostPlug.vertices f e H).toFun) =
          ((H.target x).map (Port.cast hi ho)).map
            (Replacement.insert D (f.edges.toFun e) (H.reboundary hi ho))
        simp only [Net.Vertex, Net.reboundary, List.map_map]
        exact List.map_congr_left (fun v _ => HostPlug.map_insert f e hi ho H v)

end Net
end Hypernets.Graph

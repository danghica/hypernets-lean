import Hypernets.Graph.ExpansionPlug
import Hypernets.Graph.Parallel

/-! Addressed replacement through arbitrary ordered parallel assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.ParallelPlug
universe u
open ExpansionPlug (cast_vertex cast_internalLabel cast_edgeLabel cast_source cast_target)
variable {L : Type} {Op : Type u} {σ : Signature L Op} {X : Type} {I O : X → List L}
    (F : (b : X) → Net σ (I b) (O b))
    (a : X) (e : (F a).Edge)
    (H : Net σ (σ.input ((F a).edgeLabel e)) (σ.output ((F a).edgeLabel e)))

/-- Change just the selected component by an ordinary shallow replacement. -/
noncomputable def family (b : X) :
    Net σ (I b) (O b) := by
  classical
  exact if eq : b = a then eq ▸ (F a).plug e H else F b

@[simp] theorem family_same : family F a e H a = (F a).plug e H := by
  simp [family]

@[simp] theorem family_other (b : X) (ne : b ≠ a) : family F a e H b = F b := by
  simp [family,ne]

/-- Regroup the newly inserted internal vertices into the selected component. -/
noncomputable def vertexTo : ((Σ b, (F b).Internal) ⊕ H.Internal) →
    (Σ b, (family F a e H b).Internal) := by
  classical
  intro v
  rcases v with ⟨b,v⟩ | v
  · by_cases eq : b = a
    · subst b; exact ⟨a,by simpa using (Sum.inl v : (F a).Internal ⊕ H.Internal)⟩
    · exact ⟨b,by simpa [family_other F a e H b eq] using v⟩
  · exact ⟨a,by simpa using (Sum.inr v : (F a).Internal ⊕ H.Internal)⟩

/-- The selected component's old vertex receives the retained-vertex tag. -/
theorem vertexTo_same (v : (F a).Internal) : vertexTo F a e H (.inl ⟨a,v⟩) =
    ⟨a,cast (congrArg Net.Internal (family_same F a e H).symm)
      (Sum.inl v : (F a).Internal ⊕ H.Internal)⟩ := by simp [vertexTo]

/-- An unchanged component keeps its vertex tag. -/
theorem vertexTo_other (b : X) (ne : b ≠ a) (v : (F b).Internal) :
    vertexTo F a e H (.inl ⟨b,v⟩) =
      ⟨b,cast (congrArg Net.Internal (family_other F a e H b ne).symm) v⟩ := by simp [vertexTo,ne]

noncomputable def vertexFrom : (Σ b, (family F a e H b).Internal) →
    ((Σ b, (F b).Internal) ⊕ H.Internal) := by
  classical
  rintro ⟨b,v⟩
  by_cases eq : b = a
  · subst b
    have v' : (F a).Internal ⊕ H.Internal := by simpa using v
    exact match v' with | .inl w => .inl ⟨a,w⟩ | .inr w => .inr w
  · exact .inl ⟨b,by simpa [family_other F a e H b eq] using v⟩

noncomputable def vertices : Bijection
    ((Σ b, (F b).Internal) ⊕ H.Internal) (Σ b, (family F a e H b).Internal) where
  toFun := vertexTo F a e H
  invFun := vertexFrom F a e H
  left_inv v := by
    classical
    rcases v with ⟨b,v⟩ | v
    · by_cases eq : b = a
      · subst b; rw [vertexTo_same]; simp [vertexFrom]
      · rw [vertexTo_other F a e H b eq]; simp [vertexFrom,eq]
    · simp [vertexTo,vertexFrom]
  right_inv v := by
    classical
    rcases v with ⟨b,v⟩
    by_cases eq : b = a
    · subst b
      have rep : ∃ w : (F a).Internal ⊕ H.Internal,
          v = cast (congrArg Net.Internal (family_same F a e H).symm) w :=
        ⟨cast (congrArg Net.Internal (family_same F a e H)) v, by simp⟩
      obtain ⟨w,rfl⟩ := rep
      cases w <;> simp [vertexTo,vertexFrom]
    · simp [vertexTo,vertexFrom,eq]

/-- Regroup retained and inserted edges, preserving their original labels. -/
noncomputable def edgeTo : ({x : Σ b, (F b).Edge // x ≠ ⟨a,e⟩} ⊕ H.Edge) →
    (Σ b, (family F a e H b).Edge) := by
  classical
  rintro (⟨⟨b,f⟩,ne⟩ | f)
  · by_cases eq : b = a
    · subst b
      have nf : f ≠ e := fun eq => ne (congrArg (Sigma.mk a) eq)
      exact ⟨a,by simpa using (Sum.inl ⟨f,nf⟩ : Replacement.Edge (F a) e H)⟩
    · exact ⟨b,by simpa [family_other F a e H b eq] using f⟩
  · exact ⟨a,by simpa using (Sum.inr f : Replacement.Edge (F a) e H)⟩

noncomputable def edgeFrom : (Σ b, (family F a e H b).Edge) →
    ({x : Σ b, (F b).Edge // x ≠ ⟨a,e⟩} ⊕ H.Edge) := by
  classical
  rintro ⟨b,f⟩
  by_cases eq : b = a
  · subst b
    have f' : Replacement.Edge (F a) e H := by simpa using f
    exact match f' with
    | .inl f => .inl ⟨⟨a,f.val⟩,fun eq => f.property (by simpa using eq)⟩
    | .inr f => .inr f
  · exact .inl ⟨⟨b,by simpa [family_other F a e H b eq] using f⟩,
      fun h => eq (congrArg Sigma.fst h)⟩

noncomputable def edges : Bijection
    ({x : Σ b, (F b).Edge // x ≠ ⟨a,e⟩} ⊕ H.Edge) (Σ b, (family F a e H b).Edge) where
  toFun := edgeTo F a e H
  invFun := edgeFrom F a e H
  left_inv x := by
    classical
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b
        have nf : f ≠ e := fun h => ne (congrArg (Sigma.mk a) h)
        have ht : edgeTo F a e H (.inl ⟨⟨a,f⟩,ne⟩) =
            ⟨a,cast (congrArg Net.Edge (family_same F a e H).symm)
              (Sum.inl ⟨f,nf⟩ : Replacement.Edge (F a) e H)⟩ := by simp [edgeTo]
        change edgeFrom F a e H (edgeTo F a e H _) = _
        rw [ht]
        simp [edgeFrom]
      · have ht : edgeTo F a e H (.inl ⟨⟨b,f⟩,ne⟩) =
            ⟨b,cast (congrArg Net.Edge (family_other F a e H b eq).symm) f⟩ := by
          simp [edgeTo,eq]
        change edgeFrom F a e H (edgeTo F a e H _) = _
        rw [ht]
        simp [edgeFrom,eq]
    · simp [edgeTo,edgeFrom]
  right_inv x := by
    classical
    rcases x with ⟨b,f⟩
    by_cases eq : b = a
    · subst b
      have rep : ∃ w : Replacement.Edge (F a) e H,
          f = cast (congrArg Net.Edge (family_same F a e H).symm) w :=
        ⟨cast (congrArg Net.Edge (family_same F a e H)) f, by simp⟩
      obtain ⟨w,rfl⟩ := rep
      cases w <;> simp [edgeTo,edgeFrom]
    · simp [edgeTo,edgeFrom,eq]

variable {J K : List L} (B : Parallel.Boundary I O J K) (finite : Enumeration X)

/-- Vertices of an unchanged component retain their boundary attachments. -/
theorem map_other (b : X) (ne : b ≠ a) (v : (F b).Vertex) :
    Port.map (vertexTo F a e H)
      (Replacement.host (Parallel.net F B finite) ⟨a,e⟩ H (Parallel.embed F B b v)) =
    Parallel.embed (family F a e H) B b
      (cast (congrArg (fun G => G.Vertex) (family_other F a e H b ne).symm) v) := by
  rw [cast_vertex (family_other F a e H b ne).symm]
  cases v with
  | internal v => simp [Parallel.embed,Replacement.host,Port.map,vertexTo,ne]
  | input v => rfl
  | output v => rfl

/-- Old vertices of the changed component become its retained host vertices. -/
theorem map_component (v : (F a).Vertex) :
    Port.map (vertexTo F a e H)
      (Replacement.host (Parallel.net F B finite) ⟨a,e⟩ H (Parallel.embed F B a v)) =
    Parallel.embed (family F a e H) B a
      (cast (congrArg (fun G => G.Vertex) (family_same F a e H).symm)
        (Replacement.host (F a) e H v)) := by
  rw [cast_vertex (family_same F a e H).symm]
  cases v with
  | internal v => simp [Parallel.embed,Replacement.host,Port.map,vertexTo]
  | input v => rfl
  | output v => rfl

/-- The inserted graph has identical attachments before and after parallel assembly. -/
theorem map_inserted (v : H.Vertex) :
    Port.map (vertexTo F a e H) (Replacement.insert (Parallel.net F B finite) ⟨a,e⟩ H v) =
    Parallel.embed (family F a e H) B a
      (cast (congrArg (fun G => G.Vertex) (family_same F a e H).symm)
        (Replacement.insert (F a) e H v)) := by
  rw [cast_vertex (family_same F a e H).symm]
  cases v with
  | internal v => simp [Parallel.embed,Replacement.insert,Port.map,vertexTo]
  | input v =>
    simpa [cast_vertex (family_same F a e H).symm,Replacement.insert,Net.sourcePort,Parallel.net,Parallel.incidence,List.getElem_map]
      using map_component F a e H B finite ((F a).sourcePort e v)
  | output v =>
    simpa [cast_vertex (family_same F a e H).symm,Replacement.insert,Net.targetPort,Parallel.net,Parallel.incidence,List.getElem_map]
      using map_component F a e H B finite ((F a).targetPort e v)

/-- The selected component's retained edge keeps its tag. -/
theorem edgeTo_same (f : (F a).Edge) (ne : (Sigma.mk a f : (Σ b, (F b).Edge)) ≠ ⟨a,e⟩) :
    edgeTo F a e H (.inl ⟨⟨a,f⟩,ne⟩) =
      ⟨a,cast (congrArg Net.Edge (family_same F a e H).symm)
        (Sum.inl ⟨f,fun eq => ne (congrArg (Sigma.mk a) eq)⟩ : Replacement.Edge (F a) e H)⟩ := by
  simp [edgeTo]

/-- An edge in another component is untouched. -/
theorem edgeTo_other (b : X) (ne : b ≠ a) (f : (F b).Edge)
    (nf : (Sigma.mk b f : (Σ b, (F b).Edge)) ≠ ⟨a,e⟩) :
    edgeTo F a e H (.inl ⟨⟨b,f⟩,nf⟩) =
      ⟨b,cast (congrArg Net.Edge (family_other F a e H b ne).symm) f⟩ := by simp [edgeTo,ne]

/-- A newly inserted edge is assigned to the selected component. -/
theorem edgeTo_inserted (f : H.Edge) :
    edgeTo F a e H (.inr f) =
      ⟨a,cast (congrArg Net.Edge (family_same F a e H).symm)
        (Sum.inr f : Replacement.Edge (F a) e H)⟩ := by simp [edgeTo]

/-- Replacing an edge after parallel assembly agrees with first replacing it in its
component and then expanding. The proof preserves labels and all ordered ports. -/
noncomputable def iso : Iso ((Parallel.net F B finite).plug ⟨a,e⟩ H) (Parallel.net (family F a e H) B finite) where
  vertices := vertices F a e H
  edges := edges F a e H
  internal_label v := by
    classical
    change (Parallel.net (family F a e H) B finite).internalLabel (vertexTo F a e H v) = _
    rcases v with ⟨b,v⟩ | v
    · by_cases eq : b = a
      · subst b
        rw [vertexTo_same]
        exact cast_internalLabel (family_same F a e H).symm _
      · rw [vertexTo_other F a e H b eq]
        exact cast_internalLabel (family_other F a e H b eq).symm v
    · simp [vertexTo,Parallel.net,Replacement.internalLabel,cast_internalLabel (family_same F a e H).symm]
  edge_label x := by
    classical
    change (Parallel.net (family F a e H) B finite).edgeLabel (edgeTo F a e H x) = _
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        exact cast_edgeLabel (family_same F a e H).symm _
      · rw [edgeTo_other F a e H b eq]
        exact cast_edgeLabel (family_other F a e H b eq).symm f
    · rw [edgeTo_inserted]
      exact cast_edgeLabel (family_same F a e H).symm _
  source x := by
    classical
    change (((Parallel.net F B finite).plug ⟨a,e⟩ H).source x).map (Port.map (vertexTo F a e H)) =
      (Parallel.net (family F a e H) B finite).source (edgeTo F a e H x)
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        change ((((F a).source f).map _).map _).map _ = ((family F a e H a).source _).map _
        rw [cast_source (family_same F a e H).symm]
        change ((((F a).source f).map _).map _).map _ = ((((F a).source f).map _).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_component F a e H B finite v)
      · rw [edgeTo_other F a e H b eq]
        change ((((F b).source f).map _).map _).map _ = ((family F a e H b).source _).map _
        rw [cast_source (family_other F a e H b eq).symm]
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_other F a e H B finite b eq v)
    · rw [edgeTo_inserted]
      change ((H.source f).map _).map _ = ((family F a e H a).source _).map _
      rw [cast_source (family_same F a e H).symm]
      change ((H.source f).map _).map _ = (((H.source f).map _).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => map_inserted F a e H B finite v)
  target x := by
    classical
    change (((Parallel.net F B finite).plug ⟨a,e⟩ H).target x).map (Port.map (vertexTo F a e H)) =
      (Parallel.net (family F a e H) B finite).target (edgeTo F a e H x)
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        change ((((F a).target f).map _).map _).map _ = ((family F a e H a).target _).map _
        rw [cast_target (family_same F a e H).symm]
        change ((((F a).target f).map _).map _).map _ = ((((F a).target f).map _).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_component F a e H B finite v)
      · rw [edgeTo_other F a e H b eq]
        change ((((F b).target f).map _).map _).map _ = ((family F a e H b).target _).map _
        rw [cast_target (family_other F a e H b eq).symm]
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_other F a e H B finite b eq v)
    · rw [edgeTo_inserted]
      change ((H.target f).map _).map _ = ((family F a e H a).target _).map _
      rw [cast_target (family_same F a e H).symm]
      change ((H.target f).map _).map _ = (((H.target f).map _).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => map_inserted F a e H B finite v)
end Hypernets.Graph.Net.ParallelPlug


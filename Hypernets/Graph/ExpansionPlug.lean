import Hypernets.Graph.ExpansionPeel

/-! Addressed replacement inside a component of a simultaneous expansion. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net.ExpansionPlug
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (C : Net σ I O)
    (F : (b : C.Edge) → Net σ (σ.input (C.edgeLabel b)) (σ.output (C.edgeLabel b)))
    (a : C.Edge) (e : (F a).Edge)
    (H : Net σ (σ.input ((F a).edgeLabel e)) (σ.output ((F a).edgeLabel e)))

/-- Change just the selected component by an ordinary shallow replacement. -/
noncomputable def family (b : C.Edge) :
    Net σ (σ.input (C.edgeLabel b)) (σ.output (C.edgeLabel b)) := by
  classical
  exact if eq : b = a then eq ▸ (F a).plug e H else F b

@[simp] theorem family_same : family C F a e H a = (F a).plug e H := by
  simp [family]

@[simp] theorem family_other (b : C.Edge) (ne : b ≠ a) : family C F a e H b = F b := by
  simp [family,ne]

/-- Regroup the newly inserted internal vertices into the selected component. -/
noncomputable def vertexTo : ((C.expand F).plug ⟨a,e⟩ H).Internal →
    (C.expand (family C F a e H)).Internal := by
  classical
  intro v
  rcases v with (v | ⟨b,v⟩) | v
  · exact .inl v
  · by_cases eq : b = a
    · subst b; exact .inr ⟨a,by simpa using (Sum.inl v : (F a).Internal ⊕ H.Internal)⟩
    · exact .inr ⟨b,by simpa [family_other C F a e H b eq] using v⟩
  · exact .inr ⟨a,by simpa using (Sum.inr v : (F a).Internal ⊕ H.Internal)⟩

noncomputable def vertexFrom : (C.expand (family C F a e H)).Internal →
    ((C.expand F).plug ⟨a,e⟩ H).Internal := by
  classical
  rintro (v | ⟨b,v⟩)
  · exact .inl (.inl v)
  · by_cases eq : b = a
    · subst b
      have v' : (F a).Internal ⊕ H.Internal := by simpa using v
      exact match v' with | .inl w => .inl (.inr ⟨a,w⟩) | .inr w => .inr w
    · exact .inl (.inr ⟨b,by simpa [family_other C F a e H b eq] using v⟩)

noncomputable def vertices : Bijection
    ((C.expand F).plug ⟨a,e⟩ H).Internal (C.expand (family C F a e H)).Internal where
  toFun := vertexTo C F a e H
  invFun := vertexFrom C F a e H
  left_inv v := by
    classical
    rcases v with (v | ⟨b,v⟩) | v
    · rfl
    · by_cases eq : b = a
      · subst b; simp [vertexTo,vertexFrom]
      · simp [vertexTo,vertexFrom,eq]
    · simp [vertexTo,vertexFrom]
  right_inv v := by
    classical
    rcases v with v | ⟨b,v⟩
    · rfl
    · by_cases eq : b = a
      · subst b
        have rep : ∃ w : (F a).Internal ⊕ H.Internal,
            v = cast (congrArg Net.Internal (family_same C F a e H).symm) w :=
          ⟨cast (congrArg Net.Internal (family_same C F a e H)) v, by simp⟩
        obtain ⟨w,rfl⟩ := rep
        cases w <;> simp [vertexTo,vertexFrom]
      · simp [vertexTo,vertexFrom,eq]

/-- Regroup retained and inserted edges, preserving their original labels. -/
noncomputable def edgeTo : ((C.expand F).plug ⟨a,e⟩ H).Edge →
    (C.expand (family C F a e H)).Edge := by
  classical
  rintro (⟨⟨b,f⟩,ne⟩ | f)
  · by_cases eq : b = a
    · subst b
      have nf : f ≠ e := fun eq => ne (congrArg (Sigma.mk a) eq)
      exact ⟨a,by simpa using (Sum.inl ⟨f,nf⟩ : Replacement.Edge (F a) e H)⟩
    · exact ⟨b,by simpa [family_other C F a e H b eq] using f⟩
  · exact ⟨a,by simpa using (Sum.inr f : Replacement.Edge (F a) e H)⟩

noncomputable def edgeFrom : (C.expand (family C F a e H)).Edge →
    ((C.expand F).plug ⟨a,e⟩ H).Edge := by
  classical
  rintro ⟨b,f⟩
  by_cases eq : b = a
  · subst b
    have f' : Replacement.Edge (F a) e H := by simpa using f
    exact match f' with
    | .inl f => .inl ⟨⟨a,f.val⟩,fun eq => f.property (by simpa using eq)⟩
    | .inr f => .inr f
  · exact .inl ⟨⟨b,by simpa [family_other C F a e H b eq] using f⟩,
      fun h => eq (congrArg Sigma.fst h)⟩

noncomputable def edges : Bijection
    ((C.expand F).plug ⟨a,e⟩ H).Edge (C.expand (family C F a e H)).Edge where
  toFun := edgeTo C F a e H
  invFun := edgeFrom C F a e H
  left_inv x := by
    classical
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b
        have nf : f ≠ e := fun h => ne (congrArg (Sigma.mk a) h)
        have ht : edgeTo C F a e H (.inl ⟨⟨a,f⟩,ne⟩) =
            ⟨a,cast (congrArg Net.Edge (family_same C F a e H).symm)
              (Sum.inl ⟨f,nf⟩ : Replacement.Edge (F a) e H)⟩ := by simp [edgeTo]
        change edgeFrom C F a e H (edgeTo C F a e H _) = _
        rw [ht]
        simp [edgeFrom]
      · have ht : edgeTo C F a e H (.inl ⟨⟨b,f⟩,ne⟩) =
            ⟨b,cast (congrArg Net.Edge (family_other C F a e H b eq).symm) f⟩ := by
          simp [edgeTo,eq]
        change edgeFrom C F a e H (edgeTo C F a e H _) = _
        rw [ht]
        simp [edgeFrom,eq]
    · simp [edgeTo,edgeFrom]
  right_inv x := by
    classical
    rcases x with ⟨b,f⟩
    by_cases eq : b = a
    · subst b
      have rep : ∃ w : Replacement.Edge (F a) e H,
          f = cast (congrArg Net.Edge (family_same C F a e H).symm) w :=
        ⟨cast (congrArg Net.Edge (family_same C F a e H)) f, by simp⟩
      obtain ⟨w,rfl⟩ := rep
      cases w <;> simp [edgeTo,edgeFrom]
    · simp [edgeTo,edgeFrom,eq]

/-- Equality transport of a graph vertex fixes its boundary ports. -/
@[simp] theorem cast_vertex {J K} {G D : Net σ J K} (eq : G = D) (v : G.Vertex) :
    cast (congrArg (fun G => G.Vertex) eq) v = Port.map (cast (congrArg Net.Internal eq)) v := by
  cases eq
  cases v <;> rfl

/-- The carrier regrouping fixes every original host vertex. -/
theorem map_host (v : C.Vertex) :
    Port.map (vertexTo C F a e H)
      (Replacement.host (C.expand F) ⟨a,e⟩ H (Expansion.host C F v)) =
    Expansion.host C (family C F a e H) v := by cases v <;> rfl

/-- Vertices of an unchanged component retain their boundary attachments. -/
theorem map_other (b : C.Edge) (ne : b ≠ a) (v : (F b).Vertex) :
    Port.map (vertexTo C F a e H)
      (Replacement.host (C.expand F) ⟨a,e⟩ H (Expansion.insert C F b v)) =
    Expansion.insert C (family C F a e H) b
      (cast (congrArg (fun G => G.Vertex) (family_other C F a e H b ne).symm) v) := by
  rw [cast_vertex (family_other C F a e H b ne).symm]
  cases v with
  | internal v => simp [Expansion.insert,Replacement.host,Port.map,vertexTo,ne]
  | input v => simpa [Expansion.insert,Port.map] using map_host C F a e H (C.sourcePort b v)
  | output v => simpa [Expansion.insert,Port.map] using map_host C F a e H (C.targetPort b v)

/-- Old vertices of the changed component become its retained host vertices. -/
theorem map_component (v : (F a).Vertex) :
    Port.map (vertexTo C F a e H)
      (Replacement.host (C.expand F) ⟨a,e⟩ H (Expansion.insert C F a v)) =
    Expansion.insert C (family C F a e H) a
      (cast (congrArg (fun G => G.Vertex) (family_same C F a e H).symm)
        (Replacement.host (F a) e H v)) := by
  rw [cast_vertex (family_same C F a e H).symm]
  cases v with
  | internal v => simp [Expansion.insert,Replacement.host,Port.map,vertexTo]
  | input v => simpa [Expansion.insert,Replacement.host,Port.map] using map_host C F a e H (C.sourcePort a v)
  | output v => simpa [Expansion.insert,Replacement.host,Port.map] using map_host C F a e H (C.targetPort a v)

/-- The inserted graph has identical attachments before and after expansion. -/
theorem map_inserted (v : H.Vertex) :
    Port.map (vertexTo C F a e H) (Replacement.insert (C.expand F) ⟨a,e⟩ H v) =
    Expansion.insert C (family C F a e H) a
      (cast (congrArg (fun G => G.Vertex) (family_same C F a e H).symm)
        (Replacement.insert (F a) e H v)) := by
  rw [cast_vertex (family_same C F a e H).symm]
  cases v with
  | internal v => simp [Expansion.insert,Replacement.insert,Port.map,vertexTo]
  | input v =>
    simpa [cast_vertex (family_same C F a e H).symm,Replacement.insert,Net.sourcePort,Net.expand,Expansion.source,List.getElem_map]
      using map_component C F a e H ((F a).sourcePort e v)
  | output v =>
    simpa [cast_vertex (family_same C F a e H).symm,Replacement.insert,Net.targetPort,Net.expand,Expansion.target,List.getElem_map]
      using map_component C F a e H ((F a).targetPort e v)

@[simp] theorem cast_internalLabel {J K} {G D : Net σ J K} (eq : G = D) (v : G.Internal) :
    D.internalLabel (cast (congrArg Net.Internal eq) v) = G.internalLabel v := by cases eq; rfl

@[simp] theorem cast_edgeLabel {J K} {G D : Net σ J K} (eq : G = D) (f : G.Edge) :
    D.edgeLabel (cast (congrArg Net.Edge eq) f) = G.edgeLabel f := by cases eq; rfl

@[simp] theorem cast_source {J K} {G D : Net σ J K} (eq : G = D) (f : G.Edge) :
    D.source (cast (congrArg Net.Edge eq) f) =
      (G.source f).map (cast (congrArg (fun G => G.Vertex) eq)) := by cases eq; exact (List.map_id _).symm

@[simp] theorem cast_target {J K} {G D : Net σ J K} (eq : G = D) (f : G.Edge) :
    D.target (cast (congrArg Net.Edge eq) f) =
      (G.target f).map (cast (congrArg (fun G => G.Vertex) eq)) := by cases eq; exact (List.map_id _).symm

/-- The selected component's retained edge keeps its tag. -/
theorem edgeTo_same (f : (F a).Edge) (ne : (Sigma.mk a f : Expansion.Edge C F) ≠ ⟨a,e⟩) :
    edgeTo C F a e H (.inl ⟨⟨a,f⟩,ne⟩) =
      ⟨a,cast (congrArg Net.Edge (family_same C F a e H).symm)
        (Sum.inl ⟨f,fun eq => ne (congrArg (Sigma.mk a) eq)⟩ : Replacement.Edge (F a) e H)⟩ := by
  simp [edgeTo]

/-- An edge in another component is untouched. -/
theorem edgeTo_other (b : C.Edge) (ne : b ≠ a) (f : (F b).Edge)
    (nf : (Sigma.mk b f : Expansion.Edge C F) ≠ ⟨a,e⟩) :
    edgeTo C F a e H (.inl ⟨⟨b,f⟩,nf⟩) =
      ⟨b,cast (congrArg Net.Edge (family_other C F a e H b ne).symm) f⟩ := by simp [edgeTo,ne]

/-- A newly inserted edge is assigned to the selected component. -/
theorem edgeTo_inserted (f : H.Edge) :
    edgeTo C F a e H (.inr f) =
      ⟨a,cast (congrArg Net.Edge (family_same C F a e H).symm)
        (Sum.inr f : Replacement.Edge (F a) e H)⟩ := by simp [edgeTo]

/-- Replacing an edge after expansion agrees with first replacing it in its
component and then expanding. The proof preserves labels and all ordered ports. -/
noncomputable def iso : Iso ((C.expand F).plug ⟨a,e⟩ H) (C.expand (family C F a e H)) where
  vertices := vertices C F a e H
  edges := edges C F a e H
  internal_label v := by
    classical
    rcases v with (v | ⟨b,v⟩) | v
    · rfl
    · by_cases eq : b = a
      · subst b
        simp [vertices,vertexTo,Net.expand,Expansion.internalLabel,Replacement.internalLabel,cast_internalLabel (family_same C F a e H).symm]
      · simp [vertices,vertexTo,Net.expand,Expansion.internalLabel,Replacement.internalLabel,eq,cast_internalLabel (family_other C F a e H b eq).symm]
    · simp [vertices,vertexTo,Net.expand,Expansion.internalLabel,Replacement.internalLabel,cast_internalLabel (family_same C F a e H).symm]
  edge_label x := by
    classical
    change (C.expand (family C F a e H)).edgeLabel (edgeTo C F a e H x) = _
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        exact cast_edgeLabel (family_same C F a e H).symm _
      · rw [edgeTo_other C F a e H b eq]
        exact cast_edgeLabel (family_other C F a e H b eq).symm f
    · rw [edgeTo_inserted]
      exact cast_edgeLabel (family_same C F a e H).symm _
  source x := by
    classical
    change (((C.expand F).plug ⟨a,e⟩ H).source x).map (Port.map (vertexTo C F a e H)) =
      (C.expand (family C F a e H)).source (edgeTo C F a e H x)
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        change ((((F a).source f).map _).map _).map _ = ((family C F a e H a).source _).map _
        rw [cast_source (family_same C F a e H).symm]
        change ((((F a).source f).map _).map _).map _ = ((((F a).source f).map _).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_component C F a e H v)
      · rw [edgeTo_other C F a e H b eq]
        change ((((F b).source f).map _).map _).map _ = ((family C F a e H b).source _).map _
        rw [cast_source (family_other C F a e H b eq).symm]
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_other C F a e H b eq v)
    · rw [edgeTo_inserted]
      change ((H.source f).map _).map _ = ((family C F a e H a).source _).map _
      rw [cast_source (family_same C F a e H).symm]
      change ((H.source f).map _).map _ = (((H.source f).map _).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => map_inserted C F a e H v)
  target x := by
    classical
    change (((C.expand F).plug ⟨a,e⟩ H).target x).map (Port.map (vertexTo C F a e H)) =
      (C.expand (family C F a e H)).target (edgeTo C F a e H x)
    rcases x with ⟨⟨b,f⟩,ne⟩ | f
    · by_cases eq : b = a
      · subst b; rw [edgeTo_same]
        change ((((F a).target f).map _).map _).map _ = ((family C F a e H a).target _).map _
        rw [cast_target (family_same C F a e H).symm]
        change ((((F a).target f).map _).map _).map _ = ((((F a).target f).map _).map _).map _
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_component C F a e H v)
      · rw [edgeTo_other C F a e H b eq]
        change ((((F b).target f).map _).map _).map _ = ((family C F a e H b).target _).map _
        rw [cast_target (family_other C F a e H b eq).symm]
        simp only [List.map_map]
        exact List.map_congr_left (fun v _ => map_other C F a e H b eq v)
    · rw [edgeTo_inserted]
      change ((H.target f).map _).map _ = ((family C F a e H a).target _).map _
      rw [cast_target (family_same C F a e H).symm]
      change ((H.target f).map _).map _ = (((H.target f).map _).map _).map _
      simp only [List.map_map]
      exact List.map_congr_left (fun v _ => map_inserted C F a e H v)
end Hypernets.Graph.Net.ExpansionPlug


import Hypernets.Copying.ArithmeticReductionPlug

/-! Simultaneous expansion preserves the full arithmetic deletion certificate. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic.Reduction
open Graph
variable {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e)
    {head : (F hole).Edge} {result : Nat}

def equalIso {J L} {A B : Hypernet d J L} (eq : A = B) : DeepIso B A := by
  cases eq; exact DeepIso.refl _

noncomputable def fiberVertices (a : Reduction (F hole) (K hole) head result) (e : C.Edge) :
    (K e).Internal → (F e).Internal := by
  classical
  exact if eq : e = hole then eq ▸ a.vertices else (equalIso (others e eq)).vertices.toFun

noncomputable def fiberEdges (a : Reduction (F hole) (K hole) head result) (e : C.Edge) :
    (K e).Edge → (F e).Edge := by
  classical
  exact if eq : e = hole then eq ▸ a.edges else (equalIso (others e eq)).edges.toFun

theorem fiber_vertices_same (a : Reduction (F hole) (K hole) head result) :
    fiberVertices C F K hole others a hole = a.vertices := by simp [fiberVertices]

theorem fiber_edges_same (a : Reduction (F hole) (K hole) head result) :
    fiberEdges C F K hole others a hole = a.edges := by simp [fiberEdges]

noncomputable def expansionVertices (a : Reduction (F hole) (K hole) head result) :
    (C.expand K).Internal → (C.expand F).Internal :=
  Sum.map id (fun ⟨e,x⟩ => ⟨e,fiberVertices C F K hole others a e x⟩)

noncomputable def expansionEdges (a : Reduction (F hole) (K hole) head result) :
    (C.expand K).Edge → (C.expand F).Edge :=
  fun ⟨e,x⟩ => ⟨e,fiberEdges C F K hole others a e x⟩

theorem expansion_port (a : Reduction (F hole) (K hole) head result) (e : C.Edge) (v : (K e).Vertex) :
    Port.map (expansionVertices C F K hole others a) (Net.Expansion.insert C K e v) =
      Net.Expansion.insert C F e (Port.map (fiberVertices C F K hole others a e) v) := by
  cases v with
  | internal x => rfl
  | input i =>
    simp only [Net.Expansion.insert,Net.Expansion.host,Port.map]
    cases C.sourcePort e i <;> rfl
  | output i =>
    simp only [Net.Expansion.insert,Net.Expansion.host,Port.map]
    cases C.targetPort e i <;> rfl

theorem expansion_internal (e : C.Edge) (x : (F e).Internal) {v : (F e).Vertex}
    (eq : Net.Expansion.insert C F e v = .internal (.inr ⟨e,x⟩)) : v = .internal x := by
  cases v with
  | internal y => exact congrArg Port.internal (eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Port.internal.inj eq))).2)
  | input i =>
    simp only [Net.Expansion.insert,Net.Expansion.host] at eq
    cases hv : C.sourcePort e i <;> simp [hv,Port.map] at eq
  | output i =>
    simp only [Net.Expansion.insert,Net.Expansion.host] at eq
    cases hv : C.targetPort e i <;> simp [hv,Port.map] at eq

theorem expansion_target (closed : InternalTargets (F hole) head) (x) :
    Port.internal x ∈ (C.expand F).target ⟨hole,head⟩ ↔
      ∃ y, x = .inr ⟨hole,y⟩ ∧ Port.internal y ∈ (F hole).target head := by
  constructor
  · intro h
    obtain ⟨v,hv,eq⟩ := List.mem_map.mp h
    obtain ⟨y,rfl⟩ := closed v hv
    exact ⟨y,(Port.internal.inj eq).symm,hv⟩
  · rintro ⟨y,rfl,hy⟩; exact List.mem_map_of_mem hy

theorem expansion_adjacent_same (closed : InternalTargets (F hole) head) (e : (F hole).Edge) :
    (C.expand F).Adjacent ⟨hole,head⟩ ⟨hole,e⟩ ↔ (F hole).Adjacent head e := by
  constructor
  · rintro ⟨v,hv,hw⟩
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    obtain ⟨x,rfl⟩ := closed u hu
    obtain ⟨w,hw,eq⟩ := List.mem_map.mp hw
    exact ⟨.internal x,hu,(expansion_internal C F hole x eq) ▸ hw⟩
  · exact (MatchEmbedding.expand C F hole).adjacent

theorem expansion_adjacent_other (closed : InternalTargets (F hole) head) {b : C.Edge}
    (ne : b ≠ hole) (e : (F b).Edge) :
    ¬ (C.expand F).Adjacent ⟨hole,head⟩ ⟨b,e⟩ := by
  rintro ⟨v,hv,hw⟩
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  obtain ⟨x,rfl⟩ := closed u hu
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp hw
  cases w with
  | internal y => exact ne (Sigma.mk.inj (Sum.inr.inj (Port.internal.inj eq))).1
  | input i =>
    simp only [Net.Expansion.insert,Net.Expansion.host] at eq
    cases hv : C.sourcePort b i <;> simp [hv,Port.map] at eq
  | output i =>
    simp only [Net.Expansion.insert,Net.Expansion.host] at eq
    cases hv : C.targetPort b i <;> simp [hv,Port.map] at eq

theorem expansion_closed (closed : InternalTargets (F hole) head) :
    InternalTargets (C.expand F) ⟨hole,head⟩ := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  obtain ⟨x,rfl⟩ := closed w hw
  exact ⟨.inr ⟨hole,x⟩,rfl⟩

noncomputable def expand (a : Reduction (F hole) (K hole) head result)
    (closed : InternalTargets (F hole) head) :
    Reduction (C.expand F) (C.expand K) ⟨hole,head⟩ result := by
  classical
  have vi (e) : Function.Injective (fiberVertices C F K hole others a e) := by
    by_cases eq : e = hole
    · subst e; simpa only [fiber_vertices_same] using a.vertex_injective
    · simp only [fiberVertices,dite_eq_right eq]
      exact fun _ _ h => (equalIso (others e eq)).vertices.injective h
  have ei (e) : Function.Injective (fiberEdges C F K hole others a e) := by
    by_cases eq : e = hole
    · subst e; simpa only [fiber_edges_same] using a.edge_injective
    · simp only [fiberEdges,dite_eq_right eq]
      exact fun _ _ h => (equalIso (others e eq)).edges.injective h
  refine {
    vertices := expansionVertices C F K hole others a
    vertex_injective := ?_
    vertex_range := ?_
    edges := expansionEdges C F K hole others a
    edge_injective := ?_
    edge_range := ?_
    internal_label := ?_
    edge_head := ?_
    edge_other := ?_
    source := ?_
    target_head := ?_
    target_other := ?_ }
  · intro x y eq
    cases x with
    | inl x => cases y <;> cases eq; rfl
    | inr x =>
      cases y with
      | inl y => cases eq
      | inr y =>
        rcases x with ⟨b,x⟩; rcases y with ⟨c,y⟩
        have h := Sigma.mk.inj (Sum.inr.inj eq)
        cases h.1
        exact congrArg (fun z => Sum.inr (Sigma.mk b z)) (vi b (eq_of_heq h.2))
  · intro x
    rw [expansion_target C F hole closed]
    cases x with
    | inl x =>
      constructor
      · rintro _ ⟨y,eq,_⟩; cases eq
      · intro _; exact ⟨.inl x,rfl⟩
    | inr x =>
      rcases x with ⟨b,x⟩
      by_cases eq : b = hole
      · subst b
        constructor
        · rintro ⟨y,hy⟩ ⟨z,hz,mem⟩
          have zx := eq_of_heq (Sigma.mk.inj (Sum.inr.inj hz)).2
          subst z
          cases y with
          | inl y => cases hy
          | inr y =>
            rcases y with ⟨b,y⟩
            have bh := (Sigma.mk.inj (Sum.inr.inj hy)).1
            subst b
            have yy := eq_of_heq (Sigma.mk.inj (Sum.inr.inj hy)).2
            rw [fiber_vertices_same] at yy
            exact (a.vertex_range x).mp ⟨y,yy⟩ mem
        · intro hn
          obtain ⟨y,hy⟩ := (a.vertex_range x).mpr (fun h => hn ⟨x,rfl,h⟩)
          refine ⟨.inr ⟨hole,y⟩,?_⟩
          change (Sum.inr ⟨hole,fiberVertices C F K hole others a hole y⟩ : (C.expand F).Internal) = _
          rw [fiber_vertices_same,hy]
      · constructor
        · rintro _ ⟨y,hy,_⟩; exact eq (Sigma.mk.inj (Sum.inr.inj hy)).1
        · intro _
          refine ⟨.inr ⟨b,(equalIso (others b eq)).vertices.invFun x⟩,?_⟩
          simp [expansionVertices,fiberVertices,eq,(equalIso (others b eq)).vertices.right_inv]
  · rintro ⟨b,x⟩ ⟨c,y⟩ eq
    have h := Sigma.mk.inj eq
    cases h.1
    exact congrArg (Sigma.mk b) (ei b (eq_of_heq h.2))
  · rintro ⟨b,e⟩
    by_cases eq : b = hole
    · subst b
      rw [expansion_adjacent_same C F hole closed,← a.edge_range]
      constructor
      · rintro ⟨⟨b,y⟩,hy⟩
        have bh := (Sigma.mk.inj hy).1
        subst b
        have yy := eq_of_heq (Sigma.mk.inj hy).2
        rw [fiber_edges_same] at yy
        exact ⟨y,yy⟩
      · rintro ⟨y,hy⟩
        refine ⟨⟨hole,y⟩,?_⟩
        change (⟨hole,fiberEdges C F K hole others a hole y⟩ : (C.expand F).Edge) = _
        rw [fiber_edges_same,hy]
    · constructor
      · intro _; exact expansion_adjacent_other C F hole closed eq e
      · intro _
        refine ⟨⟨b,(equalIso (others b eq)).edges.invFun e⟩,?_⟩
        simp [expansionEdges,fiberEdges,eq,(equalIso (others b eq)).edges.right_inv]
  · intro x
    cases x with
    | inl x => rfl
    | inr x =>
      rcases x with ⟨b,x⟩
      by_cases eq : b = hole
      · subst b
        change (K hole).internalLabel x = (F hole).internalLabel (fiberVertices C F K hole others a hole x)
        rw [fiber_vertices_same]; exact a.internal_label x
      · change (K b).internalLabel x = (F b).internalLabel (fiberVertices C F K hole others a b x)
        simp only [fiberVertices,dite_eq_right eq]
        exact (equalIso (others b eq)).internal_label x |>.symm
  · rintro ⟨b,e⟩ eq
    have bh := (Sigma.mk.inj eq).1
    subst b
    have ee := eq_of_heq (Sigma.mk.inj eq).2
    rw [fiber_edges_same] at ee
    exact a.edge_head e ee
  · rintro ⟨b,e⟩ ne
    by_cases eq : b = hole
    · subst b
      change LabelEquiv d ((K hole).edgeLabel e) ((F hole).edgeLabel (fiberEdges C F K hole others a hole e))
      rw [fiber_edges_same]
      apply a.edge_other e
      intro h; apply ne
      change (⟨hole,fiberEdges C F K hole others a hole e⟩ : (C.expand F).Edge) = _
      rw [fiber_edges_same,h]
    · change LabelEquiv d ((K b).edgeLabel e) ((F b).edgeLabel (fiberEdges C F K hole others a b e))
      simp only [fiberEdges,dite_eq_right eq]
      exact (equalIso (others b eq)).edge_label e
  · rintro ⟨b,e⟩
    change (((K b).source e).map (Net.Expansion.insert C K b)).map (Port.map (expansionVertices C F K hole others a)) = _
    rw [List.map_map]
    have inside : ((K b).source e).map (Port.map (fiberVertices C F K hole others a b)) =
        (F b).source (fiberEdges C F K hole others a b e) := by
      by_cases eq : b = hole
      · subst b; rw [fiber_vertices_same,fiber_edges_same]; exact a.source e
      · simpa only [fiberVertices,fiberEdges,dite_eq_right eq] using (equalIso (others b eq)).source e
    calc
      _ = (((K b).source e).map (Port.map (fiberVertices C F K hole others a b))).map (Net.Expansion.insert C F b) := by
        rw [List.map_map]; exact List.map_congr_left (fun v _ => expansion_port C F K hole others a b v)
      _ = _ := by rw [inside]; rfl
  · rintro ⟨b,e⟩ eq
    have bh := (Sigma.mk.inj eq).1
    subst b
    have ee := eq_of_heq (Sigma.mk.inj eq).2
    rw [fiber_edges_same] at ee
    change ((K hole).target e).map _ = []
    rw [a.target_head e ee]; rfl
  · rintro ⟨b,e⟩ ne
    change (((K b).target e).map (Net.Expansion.insert C K b)).map (Port.map (expansionVertices C F K hole others a)) = _
    rw [List.map_map]
    have inside : ((K b).target e).map (Port.map (fiberVertices C F K hole others a b)) =
        (F b).target (fiberEdges C F K hole others a b e) := by
      by_cases eq : b = hole
      · subst b; rw [fiber_vertices_same,fiber_edges_same]
        apply a.target_other e
        intro h; apply ne
        change (⟨hole,fiberEdges C F K hole others a hole e⟩ : (C.expand F).Edge) = _
        rw [fiber_edges_same,h]
      · simpa only [fiberVertices,fiberEdges,dite_eq_right eq] using (equalIso (others b eq)).target e
    calc
      _ = (((K b).target e).map (Port.map (fiberVertices C F K hole others a b))).map (Net.Expansion.insert C F b) := by
        rw [List.map_map]; exact List.map_congr_left (fun v _ => expansion_port C F K hole others a b v)
      _ = _ := by rw [inside]; rfl
end Hypernets.Copying.Arithmetic.Reduction

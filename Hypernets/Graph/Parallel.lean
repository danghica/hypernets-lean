import Hypernets.Graph.Isomorphism

/-! Finite parallel graph assembly with an explicitly ordered boundary.
The caller supplies typed boundary bijections; no identity wires are inserted. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph.Net
universe u
namespace Parallel
variable {L : Type} {Op : Type u} {σ : Signature L Op}
    {A : Type} {I O : A → List L} (G : ∀ a, Net σ (I a) (O a))
    {J K : List L}

/-- Each component boundary occurs exactly once in the assembled boundary.
The bijections specify order and preserve each port's type. -/
structure Boundary (I O : A → List L) (J K : List L) where
  inputs : Bijection (Σ a, Fin (I a).length) (Fin J.length)
  outputs : Bijection (Σ a, Fin (O a).length) (Fin K.length)
  input_label : ∀ a i, J[inputs.toFun ⟨a,i⟩] = (I a)[i]
  output_label : ∀ a i, K[outputs.toFun ⟨a,i⟩] = (O a)[i]

variable (B : Boundary I O J K)

abbrev Vertex := Port (Σ a, (G a).Internal) J.length K.length

/-- Tag internal vertices and scatter boundary ports through the chosen bijections. -/
def embed (a : A) : (G a).Vertex → Vertex G (J := J) (K := K)
  | .internal v => .internal ⟨a,v⟩
  | .input i => .input (B.inputs.toFun ⟨a,i⟩)
  | .output i => .output (B.outputs.toFun ⟨a,i⟩)

/-- Every assembled vertex has a unique component and component vertex. -/
def vertices : Bijection (Σ a, (G a).Vertex) (Vertex G (J := J) (K := K)) where
  toFun x := embed G B x.1 x.2
  invFun
    | .internal ⟨a,v⟩ => ⟨a,.internal v⟩
    | .input i => let x := B.inputs.invFun i; ⟨x.1,.input x.2⟩
    | .output i => let x := B.outputs.invFun i; ⟨x.1,.output x.2⟩
  left_inv := by
    rintro ⟨a,v⟩
    cases v with
    | internal v => rfl
    | input i => exact congrArg (fun x : Σ a, Fin (I a).length =>
        (⟨x.1,Port.input x.2⟩ : Σ a, (G a).Vertex)) (B.inputs.left_inv ⟨a,i⟩)
    | output i => exact congrArg (fun x : Σ a, Fin (O a).length =>
        (⟨x.1,Port.output x.2⟩ : Σ a, (G a).Vertex)) (B.outputs.left_inv ⟨a,i⟩)
  right_inv := by
    intro v
    cases v with
    | internal v => rfl
    | input i => simp [embed, B.inputs.right_inv]
    | output i => simp [embed, B.outputs.right_inv]

@[simp] theorem embed_isInput (a : A) (v : (G a).Vertex) :
    (embed G B a v).IsInput ↔ v.IsInput := by cases v <;> rfl

@[simp] theorem embed_isOutput (a : A) (v : (G a).Vertex) :
    (embed G B a v).IsOutput ↔ v.IsOutput := by cases v <;> rfl

theorem embed_injective (a : A) {v w : (G a).Vertex}
    (eq : embed G B a v = embed G B a w) : v = w := by
  have h : (⟨a,v⟩ : Σ a, (G a).Vertex) = ⟨a,w⟩ := (vertices G B).injective eq
  cases h
  rfl

theorem embed_label (a : A) (v : (G a).Vertex) :
    Port.label (I := J) (O := K) (fun x : Σ a, (G a).Internal => (G x.1).internalLabel x.2)
      (embed G B a v) = (G a).vertexLabel v := by
  cases v with
  | internal v => rfl
  | input i => exact B.input_label a i
  | output i => exact B.output_label a i

/-- Transport a family of incidence lists into the assembled vertex set. -/
def incidence (f : ∀ a, (G a).Edge → List (G a).Vertex) (e : Σ a, (G a).Edge) :
    List (Vertex G (J := J) (K := K)) := (f e.1 e.2).map (embed G B e.1)

theorem incidence_nodup (f : ∀ a, (G a).Edge → List (G a).Vertex)
    (h : ∀ a e, (f a e).Nodup) (e : Σ a, (G a).Edge) : (incidence G B f e).Nodup :=
  nodup_map_on (h _ _) (fun _ _ _ _ eq => embed_injective G B _ eq)

theorem incidence_unique (f : ∀ a, (G a).Edge → List (G a).Vertex)
    (h : ∀ a {v e e'}, v ∈ f a e → v ∈ f a e' → e = e')
    {v : Vertex G (J := J) (K := K)} {e e' : Σ a, (G a).Edge}
    (he : v ∈ incidence G B f e) (he' : v ∈ incidence G B f e') : e = e' := by
  obtain ⟨a,e⟩ := e
  obtain ⟨b,e'⟩ := e'
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp he
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp he'
  have pair : (⟨b,y⟩ : Σ a, (G a).Vertex) = ⟨a,x⟩ := (vertices G B).injective eq
  have tags := congrArg Sigma.fst pair
  dsimp at tags
  subst b
  have xy : y = x := embed_injective G B a eq
  subst y
  exact congrArg (Sigma.mk a) (h a hx hy)

/-- Coverage transports through the vertex bijection for either boundary predicate. -/
theorem incidence_coverage (f : ∀ a, (G a).Edge → List (G a).Vertex)
    (P : ∀ a, (G a).Vertex → Prop) (Q : Vertex G (J := J) (K := K) → Prop)
    (preserve : ∀ a v, Q (embed G B a v) ↔ P a v)
    (cover : ∀ a v, (∃ e, v ∈ f a e) ↔ P a v) (v : Vertex G (J := J) (K := K)) :
    (∃ e, v ∈ incidence G B f e) ↔ Q v := by
  constructor
  · rintro ⟨⟨a,e⟩,h⟩
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp h
    exact (preserve a w).mpr ((cover a w).mp ⟨e,hw⟩)
  · intro hv
    have eq := (vertices G B).right_inv v
    -- Use the inverse without selecting names for the component carriers.
    generalize hx : (vertices G B).invFun v = x at eq
    obtain ⟨a,w⟩ := x
    change embed G B a w = v at eq
    obtain ⟨e,he⟩ := (cover a w).mpr ((preserve a w).mp (eq ▸ hv))
    exact ⟨⟨a,e⟩,eq ▸ List.mem_map_of_mem he⟩

/-- Assemble a finite family, with exactly the chosen ordered interface. -/
@[reducible] def net (finite : Enumeration A) : Net σ J K where
  Internal := Σ a, (G a).Internal
  Edge := Σ a, (G a).Edge
  finiteInternal := finite.sigma (fun a => (G a).finiteInternal)
  finiteEdge := finite.sigma (fun a => (G a).finiteEdge)
  internalLabel v := (G v.1).internalLabel v.2
  edgeLabel e := (G e.1).edgeLabel e.2
  source := incidence G B (fun a => (G a).source)
  target := incidence G B (fun a => (G a).target)
  source_nodup := incidence_nodup G B _ (fun a => (G a).source_nodup)
  target_nodup := incidence_nodup G B _ (fun a => (G a).target_nodup)
  source_unique := incidence_unique G B _ (fun a => (G a).source_unique)
  target_unique := incidence_unique G B _ (fun a => (G a).target_unique)
  source_coverage := incidence_coverage G B _ (fun _ v => ¬ v.IsOutput) (fun v => ¬ v.IsOutput)
    (by intro a v; simp) (fun a => (G a).source_coverage)
  target_coverage := incidence_coverage G B _ (fun _ v => ¬ v.IsInput) (fun v => ¬ v.IsInput)
    (by intro a v; simp) (fun a => (G a).target_coverage)
  source_typed e := by
    simp only [incidence, List.map_map]
    have eq : (fun v => Port.label (I := J) (O := K)
        (fun x : Σ a, (G a).Internal => (G x.1).internalLabel x.2) (embed G B e.1 v)) =
        (G e.1).vertexLabel := funext (embed_label G B e.1)
    simpa only [Function.comp_def, eq, vertexLabel] using (G e.1).source_typed e.2
  target_typed e := by
    simp only [incidence, List.map_map]
    have eq : (fun v => Port.label (I := J) (O := K)
        (fun x : Σ a, (G a).Internal => (G x.1).internalLabel x.2) (embed G B e.1 v)) =
        (G e.1).vertexLabel := funext (embed_label G B e.1)
    simpa only [Function.comp_def, eq, vertexLabel] using (G e.1).target_typed e.2
/-- Parallel components cannot acquire adjacency through a boundary permutation. -/
theorem adjacent_tag (finite : Enumeration A) {a b : A} {e : (G a).Edge} {f : (G b).Edge}
    (h : (net G B finite).Adjacent ⟨a,e⟩ ⟨b,f⟩) : a = b := by
  obtain ⟨v,hv,hw⟩ := h
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hw
  have pair : (⟨b,y⟩ : Σ a, (G a).Vertex) = ⟨a,x⟩ := (vertices G B).injective eq
  exact (congrArg Sigma.fst pair).symm

/-- Within a component, adjacency is exactly the original adjacency. -/
theorem adjacent_same (finite : Enumeration A) (a : A) (e f : (G a).Edge) :
    (net G B finite).Adjacent ⟨a,e⟩ ⟨a,f⟩ ↔ (G a).Adjacent e f := by
  constructor
  · rintro ⟨v,hv,hw⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp hw
    have yx := embed_injective G B a eq
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨v,hv,hw⟩
    exact ⟨embed G B a v,List.mem_map_of_mem hv,List.mem_map_of_mem hw⟩

/-- A path remains inside the component in which it starts. -/
theorem path_tags (finite : Enumeration A) {es : List (Σ a, (G a).Edge)}
    (h : (net G B finite).Path es) : ∀ e ∈ es, ∀ f ∈ es, e.1 = f.1 := by
  induction es with
  | nil => simp
  | cons e es ih =>
    cases es with
    | nil => simp
    | cons f fs =>
      obtain ⟨adj,tail⟩ := path_pair_iff.mp h
      have tags := adjacent_tag G B finite adj
      have rest := ih tail
      intro x hx y hy
      rcases List.mem_cons.mp hx with hx | hx
      · subst x
        rcases List.mem_cons.mp hy with hy | hy
        · subst y; rfl
        · exact tags.trans (rest f (by simp) y hy)
      · rcases List.mem_cons.mp hy with hy | hy
        · subst y; exact (rest x hx f (by simp)).trans tags.symm
        · exact rest x hx y hy

/-- Exact path preservation and reflection under a component inclusion. -/
theorem path_same (finite : Enumeration A) (a : A) (es : List (G a).Edge) :
    (net G B finite).Path (es.map (Sigma.mk a)) ↔ (G a).Path es := by
  induction es with
  | nil => constructor <;> intro h <;> cases h
  | cons e es ih =>
    cases es with
    | nil => exact ⟨fun _ => .single _, fun _ => .single _⟩
    | cons f es =>
      constructor
      · intro h
        cases h with
        | cons adj tail => exact .cons ((adjacent_same G B finite a e f).mp adj) (ih.mp tail)
      · intro h
        cases h with
        | cons adj tail => exact .cons ((adjacent_same G B finite a e f).mpr adj) (ih.mpr tail)

/-- A label property holds of the assembly exactly when it holds in every component. -/
theorem labels_iff (finite : Enumeration A) (P : Op → Prop) :
    (∀ e, P ((net G B finite).edgeLabel e)) ↔ ∀ a e, P ((G a).edgeLabel e) := by
  constructor
  · intro h a e; exact h ⟨a,e⟩
  · intro h e; exact h e.1 e.2

end Parallel
end Hypernets.Graph.Net

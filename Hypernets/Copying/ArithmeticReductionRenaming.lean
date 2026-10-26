import Hypernets.Copying.ArithmeticReduction

/-! Recursive renaming preserves source-relative arithmetic deletion. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic.Reduction
open Graph
variable {d I O} {G H K N : Hypernet d I O} {head : G.Edge} {result : Nat}

theorem port_comp {A B C : Type} {n m} (f : A → B) (g : B → C) (v : Port A n m) :
    Port.map (g ∘ f) v = Port.map g (Port.map f v) := by cases v <;> rfl

theorem map_ports_comp {A B C : Type} {n m} (f : A → B) (g : B → C) (vs : List (Port A n m)) :
    vs.map (Port.map (g ∘ f)) = (vs.map (Port.map f)).map (Port.map g) := by
  rw [List.map_map]
  exact List.map_congr_left (fun v _ => port_comp f g v)

/-- Re-represent the successor, retaining its exact original carrier images. -/
def targetRename (a : Reduction G H head result) (g : DeepIso K H) : Reduction G K head result where
  vertices := a.vertices ∘ g.vertices.toFun
  vertex_injective := a.vertex_injective.comp (fun _ _ h => g.vertices.injective h)
  vertex_range x := by
    rw [← a.vertex_range]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨g.vertices.toFun y,hy⟩
    · rintro ⟨y,hy⟩
      exact ⟨g.vertices.invFun y,by simpa [Function.comp_def,g.vertices.right_inv] using hy⟩
  edges := a.edges ∘ g.edges.toFun
  edge_injective := a.edge_injective.comp (fun _ _ h => g.edges.injective h)
  edge_range e := by
    rw [← a.edge_range]
    constructor
    · rintro ⟨f,hf⟩; exact ⟨g.edges.toFun f,hf⟩
    · rintro ⟨f,hf⟩
      exact ⟨g.edges.invFun f,by simpa [Function.comp_def,g.edges.right_inv] using hf⟩
  internal_label x := (g.internal_label x).symm.trans (a.internal_label _)
  edge_head e eq := (Search.primitive_equiv (g.edge_label e) _).mpr (a.edge_head _ eq)
  edge_other e ne := labelEquiv_trans d (g.edge_label e) (a.edge_other _ ne)
  source e := by
    rw [map_ports_comp,g.source]
    exact a.source _
  target_head e eq := by
    have h := g.target e
    rw [a.target_head _ eq] at h
    exact List.map_eq_nil_iff.mp h
  target_other e ne := by
    rw [map_ports_comp,g.target]
    exact a.target_other _ ne

/-- Re-represent the source and the surviving original occurrences. -/
def sourceRename (a : Reduction G H head result) (f : DeepIso G N) :
    Reduction N H (f.edges.toFun head) result where
  vertices := f.vertices.toFun ∘ a.vertices
  vertex_injective := fun _ _ h => a.vertex_injective (f.vertices.injective h)
  vertex_range x := by
    have target : Port.internal x ∈ N.target (f.edges.toFun head) ↔
        Port.internal (f.vertices.invFun x) ∈ G.target head := by
      rw [← f.target]
      constructor
      · rintro h
        obtain ⟨v,hv,eq⟩ := List.mem_map.mp h
        have eq' := congrArg (Port.map f.vertices.invFun) eq
        have inv := (Port.bijection f.vertices).left_inv v
        change Port.map f.vertices.invFun (Port.map f.vertices.toFun v) = _ at inv
        rw [inv] at eq'
        simpa only [eq',Port.map] using hv
      · intro h
        have mem := List.mem_map_of_mem (f := Port.map f.vertices.toFun) h
        simpa only [Port.map,f.vertices.right_inv] using mem
    rw [target,← a.vertex_range]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨y,by rw [← hy]; simp [f.vertices.left_inv]⟩
    · rintro ⟨y,hy⟩; exact ⟨y,by simp [hy,f.vertices.right_inv]⟩
  edges := f.edges.toFun ∘ a.edges
  edge_injective := fun _ _ h => a.edge_injective (f.edges.injective h)
  edge_range e := by
    have adj : N.Adjacent (f.edges.toFun head) e ↔ G.Adjacent head (f.edges.invFun e) := by
      simpa only [f.edges.right_inv] using f.adjacent_iff head (f.edges.invFun e)
    rw [adj,← a.edge_range]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨y,by rw [← hy]; simp [f.edges.left_inv]⟩
    · rintro ⟨y,hy⟩; exact ⟨y,by simp [hy,f.edges.right_inv]⟩
  internal_label x := (a.internal_label x).trans (f.internal_label _).symm
  edge_head e eq := a.edge_head e (f.edges.injective eq)
  edge_other e ne := labelEquiv_trans d (a.edge_other e (fun eq => ne (congrArg f.edges.toFun eq))) (f.edge_label _)
  source e := by
    rw [map_ports_comp,a.source,f.source]
    rfl
  target_head e eq := a.target_head e (f.edges.injective eq)
  target_other e ne := by
    rw [map_ports_comp]
    rw [a.target_other e (fun eq => ne (congrArg f.edges.toFun eq)),f.target]
    rfl

theorem targetRename_port (a : Reduction G H head result) (g : DeepIso K H) (v : K.Vertex) :
    Port.map (a.targetRename g).vertices v = Port.map a.vertices (Port.map g.vertices.toFun v) := port_comp g.vertices.toFun a.vertices v

theorem sourceRename_port (a : Reduction G H head result) (f : DeepIso G N) (v : H.Vertex) :
    Port.map (a.sourceRename f).vertices v = Port.map f.vertices.toFun (Port.map a.vertices v) := port_comp a.vertices f.vertices.toFun v
end Hypernets.Copying.Arithmetic.Reduction

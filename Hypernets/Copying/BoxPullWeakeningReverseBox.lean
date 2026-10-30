import Hypernets.Copying.BoxPullWeakeningReverseGeometry

/-! A box reached on the BPullW right has a genuine original box at the same
thunk input. Its original free interface may be larger; this is retained when
constructing converse beta and copying matches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.Decoration
open Graph Opening
variable {d I O} {G : Hypernet (d+1) I O} (D : Decoration G)

theorem project_label (v : D.graph.Vertex) : G.vertexLabel (D.project v) = D.graph.vertexLabel v := by
  have h := Net.Expansion.host_label G D.fill (D.project v)
  rw [D.host_project] at h
  exact h.symm

/-- A box cannot be introduced by decorating a primitive source corolla. -/
theorem right_box_origin (e : G.Edge) (x : (D.fill e).Edge) (b : Box (alphabet d))
    (label : (D.fill e).edgeLabel x = .inr b) : ∃ a, G.edgeLabel e = .inr a := by
  cases old : G.edgeLabel e with
  | inr a => exact ⟨a,rfl⟩
  | inl p =>
    have primitive : BoxPermutation.PrimitiveFootprint
        (Net.corolla (alphabet (d+1)).signature (G.edgeLabel e)) := fun _ => ⟨p,old⟩
    obtain ⟨f⟩ := (D.pair e).primitive_rigid primitive
    have eq := f.edge_label (f.edges.invFun x)
    change LabelEquiv (d+1) (G.edgeLabel e) _ at eq
    simp only [old,f.edges.right_inv,label] at eq
    exact False.elim eq

/-- The single thunk input remains exactly the original source incidence even
when the box's free output interface grows on the original left side. -/
theorem box_source_project (e : D.graph.Edge) (b : Box (alphabet d))
    (label : D.graph.edgeLabel e = .inr b) :
    (D.graph.source e).map D.project = G.source e.1 := by
  obtain ⟨a,old⟩ := D.right_box_origin e.1 e.2 b label
  have length : ((D.fill e.1).source e.2).length = 1 := by
    rw [(D.fill e.1).source_length]
    change ((alphabet (d+1)).signature.input (D.graph.edgeLabel e)).length = 1
    rw [label]
    rfl
  obtain ⟨v,src⟩ := List.length_eq_one_iff.mp length
  have member : v ∈ (D.fill e.1).source e.2 := by rw [src]; exact List.mem_cons_self
  have noint := (D.pair e.1).right_no_internal (fun x => nomatch x)
  have boundary : ∃ i, v = .input i := by
    cases v with
    | input i => exact ⟨i,rfl⟩
    | internal x => exact False.elim (noint x)
    | output i => exact False.elim ((D.fill e.1).source_not_output member trivial)
  obtain ⟨i,rfl⟩ := boundary
  have allinput : (D.fill e.1).source e.2 =
      (List.finRange ((alphabet (d+1)).signature.input (G.edgeLabel e.1)).length).map Port.input := by
    rw [src]
    have one : ((alphabet (d+1)).signature.input (G.edgeLabel e.1)).length = 1 := by rw [old]; rfl
    have unique : ∀ j : Fin ((alphabet (d+1)).signature.input (G.edgeLabel e.1)).length, j = i := by
      intro j; apply Fin.ext; have := j.isLt; have := i.isLt; omega
    have range : List.finRange ((alphabet (d+1)).signature.input (G.edgeLabel e.1)).length = [i] := by
      apply List.ext_getElem
      · simpa using one
      · intro j hj hk
        have z : j = 0 := by simp at hk; omega
        subst j
        simp only [List.getElem_finRange,List.getElem_cons_zero]
        exact unique _
    rw [range]
    rfl
  change (((D.fill e.1).source e.2).map (Net.Expansion.insert G D.fill e.1)).map D.project = _
  rw [allinput,List.map_map]
  have ports : ∀ i, D.project (Net.Expansion.insert G D.fill e.1 (.input i)) = G.sourcePort e.1 i := by
    intro i
    exact D.project_host _
  simp only [List.map_map,Function.comp_def,ports]
  exact Net.PlugUnit.sourcePort_list G e.1

/-- Reconstruct the actual left box with its original body and free interface;
only the common bound arity is identified through the typed thunk input. -/
theorem reflectBox {n k h} {B : Hypernet d [.term] (environmentInterface (n+k) h)}
    (f : Occurrence (box (bound := n) (freeVariables := k) B) D.graph) :
    ∃ k' h', ∃ C : Hypernet d [.term] (environmentInterface (n+k') h'),
      ∃ g : Occurrence (box (bound := n) (freeVariables := k') C) G,
        ∀ i, g.ports (.input i) = D.project (f.ports (.input i)) := by
  let x := f.edges (0 : Fin 1)
  have related := f.label (0 : Fin 1)
  cases eq : D.graph.edgeLabel x with
  | inl p =>
    change LabelEquiv (d+1) (.inr _) (D.graph.edgeLabel x) at related
    rw [eq] at related
    exact False.elim related
  | inr b =>
    obtain ⟨a,old⟩ := D.right_box_origin x.1 x.2 b eq
    have src : G.source x.1 = [D.project (f.ports (.input 0))] := by
      rw [← D.box_source_project x b eq,← f.source (0 : Fin 1)]
      rfl
    have typed := G.source_typed x.1
    rw [src,old] at typed
    have ty : G.vertexLabel (D.project (f.ports (.input 0))) = .thunk n :=
      (D.project_label _).trans (f.matchEmbedding.vertexLabel f.label (.input 0))
    change [G.vertexLabel (D.project (f.ports (.input 0)))] = [.thunk a.bound] at typed
    rw [ty] at typed
    have bounds : n = a.bound := Wire.thunk.inj (List.cons.inj typed).1
    rcases a with ⟨bound,k',h',C⟩
    dsimp only at bounds
    subst bound
    let g : Occurrence (box (bound := n) (freeVariables := k') C) G :=
      Occurrence.labelledCorolla G x.1 _ old
    refine ⟨k',h',C,g,?_⟩
    intro i
    have zero : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; simp_all)
    subst i
    have sg := g.source (0 : Fin 1)
    rw [Occurrence.labelledCorolla_edges] at sg
    rw [src] at sg
    exact (List.cons.inj sg).1
end Hypernets.Copying.BoxPullWeakening.Decoration

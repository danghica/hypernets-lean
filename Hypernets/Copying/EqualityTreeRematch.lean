import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Copying.AtomEqualityResolution

/-! Selected atom subtrees extend to occurrences of the unchanged equality rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Same.TreeRematch
open Graph Opening
variable {d h k} {U : ContractionTree .atom (h+2)} {T : ContractionTree .atom (k+2)}
    (f : Occurrence (U.atDepth d) (T.atDepth d))

def ports : (before U d).Vertex → (before T d).Vertex
  | .input i => if z : i.val = 0 then inputPort k 0 else
      beforeLeftVertex T d (f.ports (.input ⟨i.val+1,by have := i.isLt; simp [inputs] at this; simp; omega⟩))
  | .output i => .output i
  | .internal (.inl i) => .internal (.inl i)
  | .internal (.inr ⟨.tree,x⟩) => .internal (.inr ⟨.tree,f.internals x⟩)
  | .internal (.inr ⟨.compare,x⟩) => nomatch x
  | .internal (.inr ⟨.left,x⟩) => nomatch x
  | .internal (.inr ⟨.right,x⟩) => nomatch x
  | .internal (.inr ⟨.store,x⟩) => nomatch x

def edges : (before U d).Edge → (before T d).Edge
  | ⟨.tree,e⟩ => ⟨.tree,f.edges e⟩
  | ⟨.compare,e⟩ => ⟨.compare,e⟩
  | ⟨.left,e⟩ => ⟨.left,e⟩
  | ⟨.right,e⟩ => ⟨.right,e⟩
  | ⟨.store,e⟩ => ⟨.store,e⟩

variable (input : f.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (input1 : f.ports (.input ⟨1,by simp⟩) = .input ⟨1,by simp⟩)
    (output : f.ports (.output 0) = .output 0)
include input input1 output

theorem tree_ports (v : U.net.Vertex) :
    ports f (beforeLeftVertex U d v) = beforeLeftVertex T d (f.ports v) := by
  cases v with
  | internal x => rw [f.internal_map]; rfl
  | output i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rw [output]; rfl
  | input i =>
    have bound : i.val < h+2 := by simpa using i.isLt
    by_cases zero : i.val = 0
    · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
      subst i; rw [input]; rfl
    · by_cases one : i.val = 1
      · have eq : i = ⟨1,by simp⟩ := Fin.ext one
        subst i; rw [input1]; rfl
      · have positive : ∃ j : Fin h, i = ⟨j.val+2,by simp⟩ := by
          refine ⟨⟨i.val-2,by omega⟩,Fin.ext ?_⟩; simp; omega
        obtain ⟨j,rfl⟩ := positive
        simp [beforeLeftVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,
          beforeSource,otherInputs,inputPort,Port.map,ports,List.getElem_map]

noncomputable def embedding : MatchEmbedding (before U d) (before T d) where
  ports := ports f
  edges := edges f
  edge_injective := by
    rintro ⟨a,e⟩ ⟨b,g⟩ eq
    cases a <;> cases b <;> try (have bad := congrArg Sigma.fst eq; contradiction)
    all_goals first
      | exact congrArg (Sigma.mk _) (f.edge_injective (eq_of_heq (Sigma.mk.inj eq).2))
      | exact congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj eq).2)
  primitive := by
    rintro ⟨a,e⟩ p label
    cases a <;> try exact label
    exact f.matchEmbedding.primitive e p label
  source := by
    rintro ⟨a,e⟩
    cases a
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((U.net.source e).map (beforeLeftVertex U d)).map (ports f) =
        (T.net.source (f.edges e)).map (beforeLeftVertex T d)
      have row : (U.net.source e).map f.ports = T.net.source (f.edges e) := f.source e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => tree_ports f input input1 output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
  target := by
    rintro ⟨a,e⟩
    cases a
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((U.net.target e).map (beforeLeftVertex U d)).map (ports f) =
        (T.net.target (f.edges e)).map (beforeLeftVertex T d)
      have row : (U.net.target e).map f.ports = T.net.target (f.edges e) := f.target e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => tree_ports f input input1 output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl

noncomputable def occurrence : Occurrence (before U d) (before T d) :=
  (embedding f input input1 output).occurrence (by
    rintro ⟨a,e⟩
    cases a <;> first | exact f.label e | exact labelEquiv_refl _ _)

theorem occurrence_input : (occurrence f input input1 output).ports (inputPort h 0) = inputPort k 0 := rfl

end Hypernets.Copying.AtomEquality.Same.TreeRematch

namespace Hypernets.Copying.AtomEquality.Different.TreeRematch
open Graph Opening
variable {d n m k l} {U : ContractionTree .atom (n+1)} {V : ContractionTree .atom (m+1)}
    {T : ContractionTree .atom (k+1)} {S : ContractionTree .atom (l+1)}
    (f : Occurrence (U.atDepth d) (T.atDepth d))
    (g : Occurrence (V.atDepth d) (S.atDepth d))

def ports : (before U V d).Vertex → (before T S d).Vertex
  | .input i => if z : i.val = 0 then inputPort k l 0 else
      if left : i.val ≤ n then
        beforeLeftVertex T S d (f.ports (.input ⟨i.val,by simp; omega⟩))
      else beforeRightVertex T S d (g.ports (.input ⟨i.val-n,by
        have := i.isLt; simp [inputs] at this; simp; omega⟩))
  | .output i => .output i
  | .internal (.inl i) => .internal (.inl i)
  | .internal (.inr ⟨.tree,x⟩) => .internal (.inr ⟨.tree,f.internals x⟩)
  | .internal (.inr ⟨.treeRight,x⟩) => .internal (.inr ⟨.treeRight,g.internals x⟩)
  | .internal (.inr ⟨.compare,x⟩) => nomatch x
  | .internal (.inr ⟨.left,x⟩) => nomatch x
  | .internal (.inr ⟨.right,x⟩) => nomatch x
  | .internal (.inr ⟨.store,x⟩) => nomatch x
  | .internal (.inr ⟨.storeRight,x⟩) => nomatch x

def edges : (before U V d).Edge → (before T S d).Edge
  | ⟨.tree,e⟩ => ⟨.tree,f.edges e⟩
  | ⟨.treeRight,e⟩ => ⟨.treeRight,g.edges e⟩
  | ⟨.compare,e⟩ => ⟨.compare,e⟩
  | ⟨.left,e⟩ => ⟨.left,e⟩
  | ⟨.right,e⟩ => ⟨.right,e⟩
  | ⟨.store,e⟩ => ⟨.store,e⟩
  | ⟨.storeRight,e⟩ => ⟨.storeRight,e⟩

variable (input : f.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (output : f.ports (.output 0) = .output 0)
    (inputRight : g.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (outputRight : g.ports (.output 0) = .output 0)
include input output inputRight outputRight

omit inputRight outputRight in
theorem left_tree_ports (v : U.net.Vertex) :
    ports f g (beforeLeftVertex U V d v) = beforeLeftVertex T S d (f.ports v) := by
  cases v with
  | internal x => rw [f.internal_map]; rfl
  | output i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rw [output]; rfl
  | input i =>
    have bound : i.val < n+1 := by simpa using i.isLt
    by_cases zero : i.val = 0
    · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
      subst i; rw [input]; rfl
    · have positive : ∃ j : Fin n, i = ⟨j.val+1,by simp⟩ := by
        refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩; simp; omega
      obtain ⟨j,rfl⟩ := positive
      have le : j.val+1 ≤ n := by omega
      simp [beforeLeftVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,
        beforeSource,leftInputs,inputPort,Port.map,ports,List.getElem_map,le]

omit input output in
theorem right_tree_ports (v : V.net.Vertex) :
    ports f g (beforeRightVertex U V d v) = beforeRightVertex T S d (g.ports v) := by
  cases v with
  | internal x => rw [g.internal_map]; rfl
  | output i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rw [outputRight]; rfl
  | input i =>
    have bound : i.val < m+1 := by simpa using i.isLt
    by_cases zero : i.val = 0
    · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
      subst i; rw [inputRight]; rfl
    · have positive : ∃ j : Fin m, i = ⟨j.val+1,by simp⟩ := by
        refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩; simp; omega
      obtain ⟨j,rfl⟩ := positive
      have gt : ¬ n+j.val+1 ≤ n := by omega
      have sub : n+j.val+1-n = j.val+1 := by omega
      simp [beforeRightVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,
        beforeSource,rightInputs,inputPort,Port.map,ports,List.getElem_map,gt,sub]

noncomputable def embedding : MatchEmbedding (before U V d) (before T S d) where
  ports := ports f g
  edges := edges f g
  edge_injective := by
    rintro ⟨a,e⟩ ⟨b,q⟩ eq
    cases a <;> cases b <;> try (have bad := congrArg Sigma.fst eq; contradiction)
    all_goals first
      | exact congrArg (Sigma.mk _) (f.edge_injective (eq_of_heq (Sigma.mk.inj eq).2))
      | exact congrArg (Sigma.mk _) (g.edge_injective (eq_of_heq (Sigma.mk.inj eq).2))
      | exact congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj eq).2)
  primitive := by
    rintro ⟨a,e⟩ p label
    cases a <;> first | exact label | exact f.matchEmbedding.primitive e p label | exact g.matchEmbedding.primitive e p label
  source := by
    rintro ⟨a,e⟩
    cases a
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((U.net.source e).map (beforeLeftVertex U V d)).map (ports f g) =
        (T.net.source (f.edges e)).map (beforeLeftVertex T S d)
      have row : (U.net.source e).map f.ports = T.net.source (f.edges e) := f.source e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => left_tree_ports f g input output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((V.net.source e).map (beforeRightVertex U V d)).map (ports f g) =
        (S.net.source (g.edges e)).map (beforeRightVertex T S d)
      have row : (V.net.source e).map g.ports = S.net.source (g.edges e) := g.source e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => right_tree_ports f g inputRight outputRight v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
  target := by
    rintro ⟨a,e⟩
    cases a
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((U.net.target e).map (beforeLeftVertex U V d)).map (ports f g) =
        (T.net.target (f.edges e)).map (beforeLeftVertex T S d)
      have row : (U.net.target e).map f.ports = T.net.target (f.edges e) := f.target e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => left_tree_ports f g input output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((V.net.target e).map (beforeRightVertex U V d)).map (ports f g) =
        (S.net.target (g.edges e)).map (beforeRightVertex T S d)
      have row : (V.net.target e).map g.ports = S.net.target (g.edges e) := g.target e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => right_tree_ports f g inputRight outputRight v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl

noncomputable def occurrence : Occurrence (before U V d) (before T S d) :=
  (embedding f g input output inputRight outputRight).occurrence (by
    rintro ⟨a,e⟩
    cases a <;> first | exact f.label e | exact g.label e | exact labelEquiv_refl _ _)

theorem occurrence_input : (occurrence f g input output inputRight outputRight).ports (inputPort n m 0) = inputPort k l 0 := rfl

end Hypernets.Copying.AtomEquality.Different.TreeRematch

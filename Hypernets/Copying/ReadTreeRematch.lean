import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Copying.DereferenceReplacement

/-! A selected atom subtree extends to an occurrence of the unchanged read rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference.TreeRematch
open Graph Opening
variable {d h k} {U : ContractionTree .atom (h+1)} {T : ContractionTree .atom (k+1)}
    (f : Occurrence (U.atDepth d) (T.atDepth d))

def ports : (before U d).Vertex → (before T d).Vertex
  | .input i => if z : i.val = 0 then inputPort k 0 else
      beforeTreeVertex T d (f.ports (.input ⟨i.val,by simpa [inputs] using i.isLt⟩))
  | .output i => .output i
  | .internal (.inl i) => .internal (.inl i)
  | .internal (.inr ⟨.tree,x⟩) => .internal (.inr ⟨.tree,f.internals x⟩)
  | .internal (.inr ⟨.reader,x⟩) => nomatch x
  | .internal (.inr ⟨.inst,x⟩) => nomatch x
  | .internal (.inr ⟨.store,x⟩) => nomatch x

def edges : (before U d).Edge → (before T d).Edge
  | ⟨.tree,e⟩ => ⟨.tree,f.edges e⟩
  | ⟨.reader,e⟩ => ⟨.reader,e⟩
  | ⟨.inst,e⟩ => ⟨.inst,e⟩
  | ⟨.store,e⟩ => ⟨.store,e⟩

variable (input : f.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (output : f.ports (.output 0) = .output 0)
include input output

theorem tree_ports (v : U.net.Vertex) :
    ports f (beforeTreeVertex U d v) = beforeTreeVertex T d (f.ports v) := by
  cases v with
  | internal x => rw [f.internal_map]; rfl
  | output i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rw [output]; rfl
  | input i =>
    have bound : i.val < h+1 := by simpa using i.isLt
    by_cases zero : i.val = 0
    · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
      subst i
      rw [input]
      rfl
    · have positive : ∃ j : Fin h, i = ⟨j.val+1,by simp⟩ := by
        refine ⟨⟨i.val-1,by omega⟩,Fin.ext ?_⟩; simp; omega
      obtain ⟨j,rfl⟩ := positive
      simp [beforeTreeVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,beforeFrame,
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
    · change ((U.net.source e).map (beforeTreeVertex U d)).map (ports f) =
        (T.net.source (f.edges e)).map (beforeTreeVertex T d)
      have row : (U.net.source e).map f.ports = T.net.source (f.edges e) := f.source e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => tree_ports f input output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
  target := by
    rintro ⟨a,e⟩
    cases a
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
    · change ((U.net.target e).map (beforeTreeVertex U d)).map (ports f) =
        (T.net.target (f.edges e)).map (beforeTreeVertex T d)
      have row : (U.net.target e).map f.ports = T.net.target (f.edges e) := f.target e
      rw [← row,List.map_map,List.map_map]
      exact List.map_congr_left (fun v _ => tree_ports f input output v)
    · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl

noncomputable def occurrence : Occurrence (before U d) (before T d) :=
  (embedding f input output).occurrence (by
    rintro ⟨a,e⟩
    cases a <;> first | exact f.label e | exact labelEquiv_refl _ _)

theorem occurrence_input : (occurrence f input output).ports (inputPort h 0) = inputPort k 0 := rfl

end Hypernets.Copying.Dereference.TreeRematch

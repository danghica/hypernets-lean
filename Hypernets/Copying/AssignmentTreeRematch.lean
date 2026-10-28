import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Copying.AssignmentReplacement

/-! A selected atom subtree extends to an occurrence of the unchanged assignment rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.TreeRematch
open Graph Opening
variable {d h k O} {U : ContractionTree .atom (h+1)} {T : ContractionTree .atom (k+1)}
    (f : Occurrence (U.atDepth d) (T.atDepth d)) (G : Hypernet d [.term] O)

def ports : (before U G).Vertex → (before T G).Vertex := by
  cases d
  all_goals exact fun
  | .input i => if z : i.val = 0 then inputPort k O 0 else
      beforeTreeVertex T G (f.ports (.input ⟨i.val,by simpa [inputs] using i.isLt⟩))
  | .output i => .output i
  | .internal (.inl i) => .internal (.inl i)
  | .internal (.inr ⟨.tree,x⟩) => .internal (.inr ⟨.tree,f.internals x⟩)
  | .internal (.inr ⟨.assign,x⟩) => nomatch x
  | .internal (.inr ⟨.inst,x⟩) => nomatch x
  | .internal (.inr ⟨.store,x⟩) => nomatch x
  | .internal (.inr ⟨.value,x⟩) => .internal (.inr ⟨.value,x⟩)

def edges : (before U G).Edge → (before T G).Edge := by
  cases d
  all_goals exact fun
  | ⟨.tree,e⟩ => ⟨.tree,f.edges e⟩
  | ⟨.assign,e⟩ => ⟨.assign,e⟩
  | ⟨.inst,e⟩ => ⟨.inst,e⟩
  | ⟨.store,e⟩ => ⟨.store,e⟩
  | ⟨.value,e⟩ => ⟨.value,e⟩

variable (input : f.ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp⟩)
    (output : f.ports (.output 0) = .output 0)
include input output

theorem tree_ports (v : U.net.Vertex) :
    ports f G (beforeTreeVertex U G v) = beforeTreeVertex T G (f.ports v) := by
  cases d
  all_goals
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
        have attach : beforeTreeVertex U G (.input ⟨j.val+1,by simp⟩) = inputPort h O j.succ := by
          change Port.map Sum.inl ((beforeFrame h O).sourcePort .tree _) = _
          simp [Net.sourcePort,beforeFrame,beforeSource,otherInputs,inputPort,Port.map]
        rw [attach]
        change (if _ : j.val+1 = 0 then inputPort k O 0 else beforeTreeVertex T G (f.ports (.input ⟨j.val+1,by simp⟩))) = _
        simp

noncomputable def embedding : MatchEmbedding (before U G) (before T G) where
  ports := ports f G
  edges := edges f G
  edge_injective := by
    cases d
    all_goals
      rintro ⟨a,e⟩ ⟨b,g⟩ eq
      cases a <;> cases b <;> try (have bad := congrArg Sigma.fst eq; contradiction)
    all_goals first
      | exact congrArg (Sigma.mk _) (f.edge_injective (eq_of_heq (Sigma.mk.inj eq).2))
      | exact congrArg (Sigma.mk _) (eq_of_heq (Sigma.mk.inj eq).2)
  primitive := by
    cases d
    all_goals
      rintro ⟨a,e⟩ p label
      cases a <;> try exact label
      exact f.matchEmbedding.primitive e p label
  source := by
    cases d
    all_goals
      rintro ⟨a,e⟩
      cases a
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change ((U.net.source e).map (beforeTreeVertex U G)).map (ports f G) =
          (T.net.source (f.edges e)).map (beforeTreeVertex T G)
        have row : (U.net.source e).map f.ports = T.net.source (f.edges e) := f.source e
        rw [← row,List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => tree_ports f G input output v)
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change ((G.source e).map (Net.Expansion.insert (beforePattern _ h O) (beforeFill U G) .value)).map (ports f G) =
          (G.source e).map (Net.Expansion.insert (beforePattern _ k O) (beforeFill T G) .value)
        rw [List.map_map]
        apply List.map_congr_left
        intro v _
        cases v with
        | internal x => rfl
        | input i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rfl
        | output i =>
          have attachU : Net.Expansion.insert (beforePattern _ h O) (beforeFill U G) .value (.output i) = .output i.succ := by
            change Port.map Sum.inl ((beforeFrame h O).targetPort .value i) = _
            simp [Net.targetPort,beforeFrame,beforeTarget,valueOutputs,outputPort,Port.map,List.getElem_map]
          have attachT : Net.Expansion.insert (beforePattern _ k O) (beforeFill T G) .value (.output i) = .output i.succ := by
            change Port.map Sum.inl ((beforeFrame k O).targetPort .value i) = _
            simp [Net.targetPort,beforeFrame,beforeTarget,valueOutputs,outputPort,Port.map,List.getElem_map]
          exact (congrArg (ports f G) attachU).trans attachT.symm

  target := by
    cases d
    all_goals
      rintro ⟨a,e⟩
      cases a
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change ((U.net.target e).map (beforeTreeVertex U G)).map (ports f G) =
          (T.net.target (f.edges e)).map (beforeTreeVertex T G)
        have row : (U.net.target e).map f.ports = T.net.target (f.edges e) := f.target e
        rw [← row,List.map_map,List.map_map]
        exact List.map_congr_left (fun v _ => tree_ports f G input output v)
      · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e; rfl
      · change ((G.target e).map (Net.Expansion.insert (beforePattern _ h O) (beforeFill U G) .value)).map (ports f G) =
          (G.target e).map (Net.Expansion.insert (beforePattern _ k O) (beforeFill T G) .value)
        rw [List.map_map]
        apply List.map_congr_left
        intro v _
        cases v with
        | internal x => rfl
        | input i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; rfl
        | output i =>
          have attachU : Net.Expansion.insert (beforePattern _ h O) (beforeFill U G) .value (.output i) = .output i.succ := by
            change Port.map Sum.inl ((beforeFrame h O).targetPort .value i) = _
            simp [Net.targetPort,beforeFrame,beforeTarget,valueOutputs,outputPort,Port.map,List.getElem_map]
          have attachT : Net.Expansion.insert (beforePattern _ k O) (beforeFill T G) .value (.output i) = .output i.succ := by
            change Port.map Sum.inl ((beforeFrame k O).targetPort .value i) = _
            simp [Net.targetPort,beforeFrame,beforeTarget,valueOutputs,outputPort,Port.map,List.getElem_map]
          exact (congrArg (ports f G) attachU).trans attachT.symm

noncomputable def occurrence : Occurrence (before U G) (before T G) :=
  (embedding f G input output).occurrence (by
    cases d
    all_goals
      rintro ⟨a,e⟩
      cases a <;> first | exact f.label e | exact labelEquiv_refl _ _)

theorem occurrence_input : (occurrence f G input output).ports (inputPort h O 0) = inputPort k O 0 := by cases d <;> rfl

end Hypernets.Copying.Assignment.TreeRematch

import Hypernets.Copying.MatchEmbeddingGeometry

/-! Realise an actual complete outer occurrence as a typed one-hole graph
context. The finite complement is constructed from the matched edge and
internal-vertex images; it is not a hypothesis on which matches may rewrite. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CompleteMatchCut
open Graph
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)

def Outside (v : G.Vertex) : Prop := ∀ a : A.Internal, f.ports (.internal a) ≠ v

abbrev Internal := {v : G.Internal // Outside f (.internal v)}
abbrev RetainedEdge := {e : G.Edge // ∀ a : A.Edge, f.edges a ≠ e}
abbrev Vertex := Port (Internal f) I.length O.length

def embed : Vertex f → G.Vertex := Port.map Subtype.val

def project (v : G.Vertex) (outside : Outside f v) : Vertex f :=
  match v with
  | .internal v => .internal ⟨v,outside⟩
  | .input i => .input i
  | .output i => .output i

theorem embed_project (v : G.Vertex) (outside : Outside f v) :
    embed f (project f v outside) = v := by cases v <;> rfl

theorem embed_outside (v : Vertex f) : Outside f (embed f v) := by
  cases v with
  | internal v => exact v.property
  | input i =>
    intro a eq
    obtain ⟨e,mem⟩ := (A.target_coverage (.internal a)).mpr (by simp [Port.IsInput])
    have member := f.target_mem mem
    rw [eq] at member
    exact G.target_not_input member (by simp [embed,Port.map,Port.IsInput])
  | output i =>
    intro a eq
    obtain ⟨e,mem⟩ := (A.source_coverage (.internal a)).mpr (by simp [Port.IsOutput])
    have member := f.source_mem mem
    rw [eq] at member
    exact G.source_not_output member (by simp [embed,Port.map,Port.IsOutput])

theorem embed_injective : Function.Injective (embed f) :=
  fun _ _ eq => Port.map_injective (fun _ _ h => Subtype.ext h) eq

theorem project_embed (v : Vertex f) : project f (embed f v) (embed_outside f v) = v :=
  embed_injective f (embed_project f _ _)

theorem outside_source (e : RetainedEdge f) {v} (mem : v ∈ G.source e.val) : Outside f v := by
  intro a eq
  obtain ⟨b,source⟩ := (A.source_coverage (.internal a)).mpr (by simp [Port.IsOutput])
  exact e.property b (G.source_unique (eq ▸ f.source_mem source) mem)

theorem outside_target (e : RetainedEdge f) {v} (mem : v ∈ G.target e.val) : Outside f v := by
  intro a eq
  obtain ⟨b,target⟩ := (A.target_coverage (.internal a)).mpr (by simp [Port.IsInput])
  exact e.property b (G.target_unique (eq ▸ f.target_mem target) mem)

def retainedSource (e : RetainedEdge f) : List (Vertex f) :=
  (G.source e.val).attach.map (fun v => project f v.val (outside_source f e v.property))

def retainedTarget (e : RetainedEdge f) : List (Vertex f) :=
  (G.target e.val).attach.map (fun v => project f v.val (outside_target f e v.property))

theorem embed_retainedSource (e : RetainedEdge f) :
    (retainedSource f e).map (embed f) = G.source e.val := by
  simp [retainedSource,List.map_map,Function.comp_def,embed_project]

theorem embed_retainedTarget (e : RetainedEdge f) :
    (retainedTarget f e).map (embed f) = G.target e.val := by
  simp [retainedTarget,List.map_map,Function.comp_def,embed_project]

theorem mem_retainedSource (e : RetainedEdge f) (v : Vertex f) :
    v ∈ retainedSource f e ↔ embed f v ∈ G.source e.val := by
  rw [← embed_retainedSource f e]
  constructor
  · exact List.mem_map_of_mem
  · intro mem
    obtain ⟨w,mem,eq⟩ := List.mem_map.mp mem
    exact embed_injective f eq ▸ mem

theorem mem_retainedTarget (e : RetainedEdge f) (v : Vertex f) :
    v ∈ retainedTarget f e ↔ embed f v ∈ G.target e.val := by
  rw [← embed_retainedTarget f e]
  constructor
  · exact List.mem_map_of_mem
  · intro mem
    obtain ⟨w,mem,eq⟩ := List.mem_map.mp mem
    exact embed_injective f eq ▸ mem

theorem nodup_of_map {X Y : Type} (g : X → Y) {xs : List X} (h : (xs.map g).Nodup) : xs.Nodup :=
  (List.pairwise_map.mp h).imp (fun ne eq => ne (congrArg g eq))

theorem retainedSource_nodup (e : RetainedEdge f) : (retainedSource f e).Nodup :=
  nodup_of_map (embed f) ((embed_retainedSource f e).symm ▸ G.source_nodup e.val)

theorem retainedTarget_nodup (e : RetainedEdge f) : (retainedTarget f e).Nodup :=
  nodup_of_map (embed f) ((embed_retainedTarget f e).symm ▸ G.target_nodup e.val)

theorem project_label (v : G.Vertex) (outside : Outside f v) :
    Port.label (fun x : Internal f => G.internalLabel x.val) (project f v outside) =
      G.vertexLabel v := by cases v <;> rfl

theorem embed_label (v : Vertex f) :
    Port.label (fun x : Internal f => G.internalLabel x.val) v = G.vertexLabel (embed f v) :=
  by cases v <;> rfl

theorem outside_input (i : Fin J.length) : Outside f (f.ports (.input i)) := by
  intro a eq
  rw [f.ports_internal] at eq
  have bad := f.ports_eq_internal_iff.mp eq.symm
  cases bad

theorem outside_output (i : Fin K.length) : Outside f (f.ports (.output i)) := by
  intro a eq
  rw [f.ports_internal] at eq
  have bad := f.ports_eq_internal_iff.mp eq.symm
  cases bad

def inputPort (i : Fin J.length) : Vertex f := project f (f.ports (.input i)) (outside_input f i)
def outputPort (i : Fin K.length) : Vertex f := project f (f.ports (.output i)) (outside_output f i)

theorem embed_input (i : Fin J.length) : embed f (inputPort f i) = f.ports (.input i) :=
  embed_project f _ _
theorem embed_output (i : Fin K.length) : embed f (outputPort f i) = f.ports (.output i) :=
  embed_project f _ _

theorem inputPort_injective : Function.Injective (inputPort f) := by
  intro i j eq
  have eq := congrArg (embed f) eq
  rw [embed_input,embed_input] at eq
  exact Port.input.inj (f.ports_injective_of_not_output (by simp [Port.IsOutput])
    (by simp [Port.IsOutput]) eq)

theorem outputPort_injective : Function.Injective (outputPort f) := by
  intro i j eq
  have eq := congrArg (embed f) eq
  rw [embed_output,embed_output] at eq
  exact Port.output.inj (f.ports_injective_of_not_input (by simp [Port.IsInput])
    (by simp [Port.IsInput]) eq)

def source : Option (RetainedEdge f) → List (Vertex f)
  | none => (List.finRange J.length).map (inputPort f)
  | some e => retainedSource f e

def target : Option (RetainedEdge f) → List (Vertex f)
  | none => (List.finRange K.length).map (outputPort f)
  | some e => retainedTarget f e

def label : Option (RetainedEdge f) → (alphabet d).Symbol
  | none => primitiveLabel d (.hole ⟨0,J,K⟩)
  | some e => G.edgeLabel e.val

theorem mem_hole_source (v : Vertex f) :
    v ∈ source f none ↔ ∃ i, inputPort f i = v := by simp [source]

theorem mem_hole_target (v : Vertex f) :
    v ∈ target f none ↔ ∃ i, outputPort f i = v := by simp [target]

theorem source_nodup (e : Option (RetainedEdge f)) : (source f e).Nodup := by
  cases e with
  | none => exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => inputPort_injective f eq)
  | some e => exact retainedSource_nodup f e

theorem target_nodup (e : Option (RetainedEdge f)) : (target f e).Nodup := by
  cases e with
  | none => exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ eq => outputPort_injective f eq)
  | some e => exact retainedTarget_nodup f e

theorem source_disjoint (e : RetainedEdge f) {v : Vertex f}
    (hole : v ∈ source f none) (retained : v ∈ retainedSource f e) : False := by
  obtain ⟨i,rfl⟩ := (mem_hole_source f v).mp hole
  have mem := (mem_retainedSource f e (inputPort f i)).mp retained
  rw [embed_input] at mem
  obtain ⟨a,source⟩ := (A.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
  exact e.property a (G.source_unique (f.source_mem source) mem)

theorem target_disjoint (e : RetainedEdge f) {v : Vertex f}
    (hole : v ∈ target f none) (retained : v ∈ retainedTarget f e) : False := by
  obtain ⟨i,rfl⟩ := (mem_hole_target f v).mp hole
  have mem := (mem_retainedTarget f e (outputPort f i)).mp retained
  rw [embed_output] at mem
  obtain ⟨a,target⟩ := (A.target_coverage (.output i)).mpr (by simp [Port.IsInput])
  exact e.property a (G.target_unique (f.target_mem target) mem)

theorem source_unique {v : Vertex f} {e g : Option (RetainedEdge f)}
    (he : v ∈ source f e) (hg : v ∈ source f g) : e = g := by
  cases e with
  | none => cases g with
    | none => rfl
    | some g => exact False.elim (source_disjoint f g he hg)
  | some e => cases g with
    | none => exact False.elim (source_disjoint f e hg he)
    | some g =>
      exact congrArg some (Subtype.ext (G.source_unique
        ((mem_retainedSource f e v).mp he) ((mem_retainedSource f g v).mp hg)))

theorem target_unique {v : Vertex f} {e g : Option (RetainedEdge f)}
    (he : v ∈ target f e) (hg : v ∈ target f g) : e = g := by
  cases e with
  | none => cases g with
    | none => rfl
    | some g => exact False.elim (target_disjoint f g he hg)
  | some e => cases g with
    | none => exact False.elim (target_disjoint f e hg he)
    | some g =>
      exact congrArg some (Subtype.ext (G.target_unique
        ((mem_retainedTarget f e v).mp he) ((mem_retainedTarget f g v).mp hg)))

theorem source_coverage (v : Vertex f) :
    (∃ e, v ∈ source f e) ↔ ¬ v.IsOutput := by
  classical
  constructor
  · rintro ⟨e,mem⟩ out
    have output : (embed f v).IsOutput := by cases v <;> exact out
    cases e with
    | some e => exact G.source_not_output ((mem_retainedSource f e v).mp mem) output
    | none =>
      obtain ⟨i,eq⟩ := (mem_hole_source f v).mp mem
      obtain ⟨a,member⟩ := (A.source_coverage (.input i)).mpr (by simp [Port.IsOutput])
      have moved := f.source_mem member
      have same : f.ports (.input i) = embed f v := (embed_input f i).symm.trans (congrArg (embed f) eq)
      exact G.source_not_output (same ▸ moved) output
  · intro no
    have notOutput : ¬ (embed f v).IsOutput := by cases v <;> exact no
    obtain ⟨e,member⟩ := (G.source_coverage (embed f v)).mpr notOutput
    by_cases used : ∃ a, f.edges a = e
    · obtain ⟨a,rfl⟩ := used
      rw [← f.source a] at member
      obtain ⟨w,mem,eq⟩ := List.mem_map.mp member
      cases w with
      | internal x => exact False.elim (embed_outside f v x eq)
      | input i =>
        refine ⟨none,(mem_hole_source f v).mpr ⟨i,?_⟩⟩
        exact embed_injective f ((embed_input f i).trans eq)
      | output i => exact False.elim (A.source_not_output mem trivial)
    · let kept : RetainedEdge f := ⟨e,fun a eq => used ⟨a,eq⟩⟩
      exact ⟨some kept,(mem_retainedSource f kept v).mpr member⟩

theorem target_coverage (v : Vertex f) :
    (∃ e, v ∈ target f e) ↔ ¬ v.IsInput := by
  classical
  constructor
  · rintro ⟨e,mem⟩ input
    have isInput : (embed f v).IsInput := by cases v <;> exact input
    cases e with
    | some e => exact G.target_not_input ((mem_retainedTarget f e v).mp mem) isInput
    | none =>
      obtain ⟨i,eq⟩ := (mem_hole_target f v).mp mem
      obtain ⟨a,member⟩ := (A.target_coverage (.output i)).mpr (by simp [Port.IsInput])
      have moved := f.target_mem member
      have same : f.ports (.output i) = embed f v := (embed_output f i).symm.trans (congrArg (embed f) eq)
      exact G.target_not_input (same ▸ moved) isInput
  · intro no
    have notInput : ¬ (embed f v).IsInput := by cases v <;> exact no
    obtain ⟨e,member⟩ := (G.target_coverage (embed f v)).mpr notInput
    by_cases used : ∃ a, f.edges a = e
    · obtain ⟨a,rfl⟩ := used
      rw [← f.target a] at member
      obtain ⟨w,mem,eq⟩ := List.mem_map.mp member
      cases w with
      | internal x => exact False.elim (embed_outside f v x eq)
      | output i =>
        refine ⟨none,(mem_hole_target f v).mpr ⟨i,?_⟩⟩
        exact embed_injective f ((embed_output f i).trans eq)
      | input i => exact False.elim (A.target_not_input mem trivial)
    · let kept : RetainedEdge f := ⟨e,fun a eq => used ⟨a,eq⟩⟩
      exact ⟨some kept,(mem_retainedTarget f kept v).mpr member⟩

variable (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

include labels

theorem source_typed (e : Option (RetainedEdge f)) :
    (source f e).map (Port.label (fun x : Internal f => G.internalLabel x.val)) =
      (alphabet d).signature.input (label f e) := by
  cases e with
  | some e =>
    change (retainedSource f e).map _ = _
    have eq := congrArg (List.map G.vertexLabel) (embed_retainedSource f e)
    have result := eq.trans (G.source_typed e.val)
    simpa only [List.map_map,Function.comp_def,← embed_label,label] using result
  | none =>
    change ((List.finRange J.length).map (inputPort f)).map _ = _
    rw [List.map_map]
    dsimp only [label]
    rw [primitive_input]
    change _ = J
    have each (i : Fin J.length) :
        Port.label (fun x : Internal f => G.internalLabel x.val) (inputPort f i) = J[i] :=
      (project_label f _ _).trans (f.vertexLabel labels (.input i))
    simp only [Function.comp_def,each]
    simp [List.finRange,List.map_ofFn,Function.comp_def,List.ofFn_getElem]

theorem target_typed (e : Option (RetainedEdge f)) :
    (target f e).map (Port.label (fun x : Internal f => G.internalLabel x.val)) =
      (alphabet d).signature.output (label f e) := by
  cases e with
  | some e =>
    change (retainedTarget f e).map _ = _
    have eq := congrArg (List.map G.vertexLabel) (embed_retainedTarget f e)
    have result := eq.trans (G.target_typed e.val)
    simpa only [List.map_map,Function.comp_def,← embed_label,label] using result
  | none =>
    change ((List.finRange K.length).map (outputPort f)).map _ = _
    rw [List.map_map]
    dsimp only [label]
    rw [primitive_output]
    change _ = K
    have each (i : Fin K.length) :
        Port.label (fun x : Internal f => G.internalLabel x.val) (outputPort f i) = K[i] :=
      (project_label f _ _).trans (f.vertexLabel labels (.output i))
    simp only [Function.comp_def,each]
    simp [List.finRange,List.map_ofFn,Function.comp_def,List.ofFn_getElem]

/-- The finite context obtained by replacing this matched occurrence with one
hole. Every unmatched edge and every unmatched internal vertex is retained. -/
noncomputable def net : Hypernet d I O where
  Internal := Internal f
  Edge := Option (RetainedEdge f)
  finiteInternal := Enumeration.subtype G.finiteInternal (fun v => Outside f (.internal v))
  finiteEdge := {
    elements := none :: (Enumeration.subtype G.finiteEdge (fun e => ∀a,f.edges a ≠ e)).elements.map some
    complete e := by cases e with
      | none => simp
      | some e => exact List.mem_cons_of_mem _ (List.mem_map_of_mem
          ((Enumeration.subtype G.finiteEdge (fun e => ∀a,f.edges a ≠ e)).complete e)) }
  internalLabel x := G.internalLabel x.val
  edgeLabel := label f
  source := source f
  target := target f
  source_nodup := source_nodup f
  target_nodup := target_nodup f
  source_unique := source_unique f
  target_unique := target_unique f
  source_coverage := source_coverage f
  target_coverage := target_coverage f
  source_typed := source_typed f labels
  target_typed := target_typed f labels

end Hypernets.Copying.CompleteMatchCut

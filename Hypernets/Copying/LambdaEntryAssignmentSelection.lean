import Hypernets.Copying.LambdaEntryAssignmentFrame
import Hypernets.Copying.AssignmentEnabled

/-! Extract the complete retained assignment frame and transfer it to the
opposite actual filling. Rooted search selects that side's own stable value. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion MatchEmbedding Combined
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (none : T.NoOutputs) {h K} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] K) (f : Occurrence (Assignment.before tree G) (C.expand L))
    {v : C.Vertex} (attached : f.ports (Assignment.inputPort h K 0) = Net.Expansion.host C L v)

/-- Retained source rows use precisely the original host coordinates. -/
theorem retained_source {e : (C.expand L).Edge} (copy : Retained C L e.1) :
    (C.expand L).source e = (C.source e.1).map (Net.Expansion.host C L) := by
  obtain ⟨e,x⟩ := e
  simpa only [copy.only x] using copy.source_eq

include cert heads none attached
/-- The assignment operation, instance, unchanged full atom tree, and store
form one exact original context frame with the original ordered value wires. -/
theorem assignment_selection :
    ∃ u w o : C.Vertex,
      C.edgeLabel (f.edges (Assignment.beforeAssign tree G)).1 = primitiveLabel d (.operation (.binary .assign)) ∧
      C.edgeLabel (f.edges (Assignment.beforeInstance tree G)).1 = primitiveLabel d .instanceEdge ∧
      C.edgeLabel (f.edges (Assignment.beforeStore tree G)).1 = primitiveLabel d .store ∧
      C.source (f.edges (Assignment.beforeAssign tree G)).1 = [v] ∧
      C.target (f.edges (Assignment.beforeAssign tree G)).1 = [u,w] ∧
      C.source (f.edges (Assignment.beforeInstance tree G)).1 = [u] ∧
      C.target (f.edges (Assignment.beforeInstance tree G)).1 =
        [(assignment_tree C cert heads none tree G f attached).ports (.input ⟨0,by simp⟩)] ∧
      C.source (f.edges (Assignment.beforeStore tree G)).1 =
        [(assignment_tree C cert heads none tree G f attached).ports (.output 0)] ∧
      C.target (f.edges (Assignment.beforeStore tree G)).1 = [o] := by
  let first : (Assignment.before tree G).Vertex := by cases d <;> exact .internal (.inl (0 : Fin 4))
  let second : (Assignment.before tree G).Vertex := by cases d <;> exact .internal (.inl (1 : Fin 4))
  let old : (Assignment.before tree G).Vertex := .output ⟨0,by simp [Assignment.outputs]⟩
  have al := f.matchEmbedding.primitive (Assignment.beforeAssign tree G) (.operation (.binary .assign)) (by cases d <;> rfl)
  have il := f.matchEmbedding.primitive (Assignment.beforeInstance tree G) .instanceEdge (by cases d <;> rfl)
  have sl := f.matchEmbedding.primitive (Assignment.beforeStore tree G) .store (Assignment.store_labels tree G).1
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeAssign tree G)) = _ at al
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeInstance tree G)) = _ at il
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeStore tree G)) = _ at sl
  have asrc : (C.expand L).source (f.edges (Assignment.beforeAssign tree G)) = [Net.Expansion.host C L v] := by
    rw [← f.source]
    have src : (Assignment.before tree G).source (Assignment.beforeAssign tree G) = [Assignment.inputPort h K 0] := by cases d <;> rfl
    rw [src]; exact congrArg (fun x => [x]) attached
  have atgt : (C.expand L).target (f.edges (Assignment.beforeAssign tree G)) = [f.ports first,f.ports second] := by
    rw [← f.target]; cases d <;> rfl
  have isrc : (C.expand L).source (f.edges (Assignment.beforeInstance tree G)) = [f.ports first] := by
    rw [← f.source]; cases d <;> rfl
  have itgt : (C.expand L).target (f.edges (Assignment.beforeInstance tree G)) =
      [((Assignment.treeOccurrence tree G).comp f).ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; cases d <;> rfl
  have ssrc : (C.expand L).source (f.edges (Assignment.beforeStore tree G)) =
      [((Assignment.treeOccurrence tree G).comp f).ports (.output 0)] := by
    rw [← f.source]; cases d <;> rfl
  have stgt : (C.expand L).target (f.edges (Assignment.beforeStore tree G)) = [f.ports old] := by
    rw [← f.target]; cases d <;> rfl
  obtain ⟨hc⟩ := source_retained C cert heads (by rw [asrc]; exact List.mem_cons_self)
    (by rw [al]; intro eq; cases primitiveLabel_injective d eq)
  obtain ⟨ic⟩ := assignment_instance_retained C cert heads tree G f attached
  obtain ⟨sc⟩ := assignment_store_retained C cert heads tree G f attached
  obtain ⟨u,hu⟩ := hc.target_origin (show f.ports first ∈ _ by rw [atgt]; exact List.mem_cons_self)
  obtain ⟨w,hw⟩ := hc.target_origin (show f.ports second ∈ _ by rw [atgt]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  obtain ⟨o,ho⟩ := sc.target_origin (show f.ports old ∈ _ by rw [stgt]; exact List.mem_cons_self)
  refine ⟨u,w,o,retained_primitive C hc al,retained_primitive C ic il,retained_primitive C sc sl,?_,?_,?_,?_,?_,?_⟩
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_source C hc,asrc]; rfl
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_target C hc,atgt]
    simp only [List.map_cons,List.map_nil,hu,hw]
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_source C ic,isrc]
    exact congrArg (fun x => [x]) hu.symm
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_target C ic,itgt]
    simp only [List.map_cons,List.map_nil,assignment_tree_host]
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_source C sc,ssrc]
    simp only [List.map_cons,List.map_nil,assignment_tree_host]
  · apply (List.map_inj_right (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [← retained_target C sc,stgt]
    exact congrArg (fun x => [x]) ho.symm

/-- The opposite filling contains the same complete original atom tree. -/
noncomputable def assignment_tree_right : Occurrence (tree.atDepth d) (C.expand R) := by
  let raw := (Assignment.treeOccurrence tree G).comp f
  let across := RetainedFootprint.across C raw.matchEmbedding cert
    (assignment_tree_avoids C cert heads none tree G f attached)
  exact across.occurrence (fun e => by
    have label := across.primitive e (tree.net.edgeLabel e) rfl
    rw [label]
    exact labelEquiv_refl d _)

/-- Opposite tree ports use the same original host coordinates. -/
theorem assignment_tree_right_port (x : (tree.atDepth d).Vertex) :
    (assignment_tree_right C cert heads none tree G f attached).ports x =
      Net.Expansion.host C R ((assignment_tree C cert heads none tree G f attached).ports x) := rfl

/-- Every actual assignment match has an opposite original assignment step.
The original supplied atom tree is preserved in full; the other side's stable
value is obtained from its actual rooted search history, including a lambda
inside a shallow multi-input family. -/
theorem assignment_opposite_enabled {i : Fin I.length}
    (rooted : Search.RootedFrom (C.expand R) i (.rewrite,Net.Expansion.host C R v)) :
    ∃ H : Hypernet d I O, ∃ q,
      Rewrite (C.expand R) (Net.Expansion.host C R v) H q := by
  obtain ⟨u,w,o,al,il,sl,asrc,atgt,isrc,itgt,ssrc,stgt⟩ :=
    assignment_selection C cert heads none tree G f attached
  obtain ⟨_,a⟩ := (cert (f.edges (Assignment.beforeAssign tree G)).1).retained_of_not_hole
    (by intro h eq; rw [al] at eq; cases primitiveLabel_injective d eq)
  obtain ⟨_,b⟩ := (cert (f.edges (Assignment.beforeInstance tree G)).1).retained_of_not_hole
    (by intro h eq; rw [il] at eq; cases primitiveLabel_injective d eq)
  obtain ⟨_,c⟩ := (cert (f.edges (Assignment.beforeStore tree G)).1).retained_of_not_hole
    (by intro h eq; rw [sl] at eq; cases primitiveLabel_injective d eq)
  let g := assignment_tree_right C cert heads none tree G f attached
  apply Assignment.rooted_frame_enabled (C.expand R) tree g
    ⟨_,a.edge⟩ ⟨_,b.edge⟩ ⟨_,c.edge⟩
    ((a.primitive _).mpr al) ((b.primitive _).mpr il) ((c.primitive _).mpr sl)
    (Net.Expansion.host C R v) (Net.Expansion.host C R u)
    (g.ports (.input ⟨0,by simp⟩)) (Net.Expansion.host C R w)
    (g.ports (.output 0)) (Net.Expansion.host C R o)
    _ _ _ _ _ _ rfl rfl rooted
  · rw [a.source_eq,asrc]; rfl
  · rw [a.target_eq,atgt]; rfl
  · rw [b.source_eq,isrc]; rfl
  · rw [b.target_eq,itgt]; rfl
  · rw [c.source_eq,ssrc]; rfl
  · rw [c.target_eq,stgt]; rfl

end Hypernets.Copying.LambdaEntryOverlap

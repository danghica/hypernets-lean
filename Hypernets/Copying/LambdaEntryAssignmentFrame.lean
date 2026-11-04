import Hypernets.Copying.LambdaEntryAssignmentOverlap

/-! Complete original atom-frame extraction for assignments in lambda-entry,
closed-output fillings. Unused siblings of the actual supplied tree are
retained by the backwards no-output barrier, without pruning that tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion MatchEmbedding
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (heads : T.LambdaEntries)
    (none : T.NoOutputs) {h K} (tree : ContractionTree .atom (h+1))
    (G : Hypernet d [.term] K) (f : Occurrence (Assignment.before tree G) (C.expand L))
    {v : C.Vertex} (attached : f.ports (Assignment.inputPort h K 0) = Net.Expansion.host C L v)
include cert heads attached

/-- The original supplied store is retained along its exact selected atom
trace. This does not assert retention of the new stable value. -/
theorem assignment_store_retained :
    Nonempty (Retained C L (f.edges (Assignment.beforeStore tree G)).1) := by
  obtain ⟨n,operand⟩ := Assignment.before_operand tree G
  have mapped := StoreTrace.operand_map f.matchEmbedding operand
  change StoreTrace.Operand (C.expand L) (f.ports (Assignment.inputPort h K 0))
    (.binary .assign) 0 (f.edges (Assignment.beforeStore tree G)) n at mapped
  rw [attached] at mapped
  exact (store_operand_owner C cert heads (by intro eq; cases eq) mapped).2

include none

/-- Every sibling of the supplied atom tree is retained: each reaches its
store, and an empty-output filling cannot precede that retained store. -/
theorem assignment_tree_retained (e : tree.net.Edge) :
    Nonempty (Retained C L (f.edges (Assignment.beforeTree tree G e)).1) := by
  obtain ⟨n,path⟩ := tree.reaches_root e
  have localPath := StoreTrace.ancestor (Dereference.trace_snoc
    (path.map (Assignment.beforeTree tree G) (Assignment.tree_hop_before tree G))
    (Assignment.root_before tree G))
  exact (NoOutputOverlap.ancestor_retained C cert none
    (localPath.map f.edges (fun p => f.matchEmbedding.adjacent p))
    (assignment_store_retained C cert heads tree G f attached)).1

/-- The complete original atom tree avoids shallow holes, including its
weakening leaves and all unrelated siblings. -/
theorem assignment_tree_avoids : RetainedFootprint.AvoidsShallow C
    (((Assignment.treeOccurrence tree G).comp f).matchEmbedding) := by
  intro e hole bad
  obtain ⟨copy⟩ := assignment_tree_retained C cert heads none tree G f attached e
  have actual := f.matchEmbedding.primitive _ _ (Assignment.tree_labels tree G e).1
  have original := retained_primitive C copy actual
  change C.edgeLabel (((Assignment.treeOccurrence tree G).comp f).edges e).1 = _ at bad
  have edge : ((Assignment.treeOccurrence tree G).comp f).edges e =
      f.edges (Assignment.beforeTree tree G e) := by cases d <;> rfl
  rw [edge] at bad
  rw [original] at bad
  have eq := primitiveLabel_injective d bad
  rcases tree.labels e with weak | contraction
  · rw [weak] at eq; cases eq
  · rw [contraction] at eq; cases eq

/-- Reflect the whole actual supplied tree, preserving all original boundary
coordinates and its complete primitive labels. -/
noncomputable def assignment_tree : Occurrence (tree.atDepth d) C := by
  let raw := (Assignment.treeOccurrence tree G).comp f
  let reflect := RetainedFootprint.reflect C raw.matchEmbedding cert
    (assignment_tree_avoids C cert heads none tree G f attached)
  exact reflect.occurrence (fun e => by
    have label := reflect.primitive e (tree.net.edgeLabel e) rfl
    rw [label]
    exact labelEquiv_refl d _)

/-- The reflected tree occupies exactly its original host wires. -/
theorem assignment_tree_host (x : (tree.atDepth d).Vertex) :
    Net.Expansion.host C L ((assignment_tree C cert heads none tree G f attached).ports x) =
      ((Assignment.treeOccurrence tree G).comp f).ports x :=
  RetainedFootprint.host_port C ((Assignment.treeOccurrence tree G).comp f).matchEmbedding cert
    (assignment_tree_avoids C cert heads none tree G f attached) x

omit none in
/-- The instance introducing the selected atom is an unchanged primitive. -/
theorem assignment_instance_retained :
    Nonempty (Retained C L (f.edges (Assignment.beforeInstance tree G)).1) := by
  have source := f.matchEmbedding.head (Assignment.localMatch tree G).head
  change HeadAt (C.expand L) (f.ports (Assignment.inputPort h K 0))
    (f.edges (Assignment.localMatch tree G).headEdge) (.operation (.binary .assign)) at source
  rw [attached] at source
  obtain ⟨head⟩ := source_retained C cert heads source.2 (by
    rw [source.1]; intro eq; cases primitiveLabel_injective d eq)
  have adjacent : (Assignment.before tree G).Adjacent (Assignment.localMatch tree G).headEdge
      (Assignment.beforeInstance tree G) := by
    cases d <;> exact ⟨.internal (.inl (0 : Fin 4)),List.mem_cons_self,List.mem_cons_self⟩
  obtain ⟨w,target,src⟩ := f.matchEmbedding.adjacent adjacent
  obtain ⟨u,eq⟩ := head.target_origin target
  apply source_retained C cert heads (eq ▸ src)
  have label := f.matchEmbedding.primitive (Assignment.beforeInstance tree G) .instanceEdge (by cases d <;> rfl)
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeInstance tree G)) = _ at label
  rw [label]; intro eq; cases primitiveLabel_injective d eq

end Hypernets.Copying.LambdaEntryOverlap

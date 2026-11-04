import Hypernets.Copying.LambdaEntryAssignmentOverlap
import Hypernets.Copying.NoOutputOverlap
import Hypernets.Copying.AtomEqualityResolution

/-! Entire original atom-operation footprints remain in the common context
of a lambda-entry, closed-output template. Backward ancestry includes every
unused contraction-tree branch, not only the selected reference spine. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Opening Search.Expansion MatchEmbedding
variable {P : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge P C L R e) (heads : P.LambdaEntries)
    (none : P.NoOutputs) (closed : HoleFree (C.expand L))

include closed
/-- A retained edge of an actually hole-free expansion cannot be an
unfilled original hole. This uses its literal primitive-label reflection. -/
theorem retained_not_hole {e : (C.expand L).Edge} (copy : Retained C L e.1) :
    ∀ h, C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro h label
  have hole := (copy.primitive (.hole h)).mpr label
  have no := closed ⟨e.1,copy.edge⟩
  change LabelAll _ d ((L e.1).edgeLabel copy.edge) at no
  rw [hole] at no
  cases d <;> exact no h rfl

include cert none closed
/-- Once a downstream edge is retained, every original matched ancestor is
retained and avoids shallow holes, including branches with no selected input. -/
theorem ancestor_of_retained_not_hole {J K} {A : Hypernet d J K}
    (f : Occurrence A (C.expand L)) {a b : A.Edge}
    (path : Ancestor A a b) (last : Nonempty (Retained C L (f.edges b).1)) :
    ∀ h, C.edgeLabel (f.edges a).1 ≠ primitiveLabel d (.hole h) := by
  obtain ⟨copy⟩ := (NoOutputOverlap.ancestor_retained C cert none
    (path.map f.edges (fun p => f.matchEmbedding.adjacent p)) last).1
  exact retained_not_hole C closed copy

include heads
/-- Every edge of the complete actual read rule is retained. The selected
lookup first retains the store; all unused tree branches also reach it. -/
theorem read_avoids {h} (tree : ContractionTree .atom (h+1))
    (f : Occurrence (Dereference.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (Dereference.inputPort h 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  have operand := StoreTrace.operand_map f.matchEmbedding (Dereference.localMatch tree d).operand
  change StoreTrace.Operand (C.expand L) (f.ports (Dereference.inputPort h 0)) _ _ _ _ at operand
  rw [attached] at operand
  obtain ⟨_,store⟩ := store_operand_owner C cert heads (by intro eq; cases eq) operand
  have instancePath : Ancestor (Dereference.before tree d) (Dereference.beforeInstance tree d)
      (Dereference.beforeStore tree d) := by
    obtain ⟨n,resolve,_⟩ := Dereference.resolves_both tree d
    exact StoreTrace.ancestor resolve.1
  intro e
  apply ancestor_of_retained_not_hole C cert none closed f (b := Dereference.beforeStore tree d) _ store
  obtain ⟨part,e⟩ := e
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact .step ⟨.internal (.inl (0 : Fin 3)),List.mem_cons_self,List.mem_cons_self⟩ instancePath
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact instancePath
  · obtain ⟨n,path⟩ := tree.reaches_root e
    exact StoreTrace.ancestor (Dereference.trace_snoc (path.map (Dereference.beforeTree tree d)
      (Dereference.tree_hop_before tree d)) (Dereference.root_before tree d))
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact .refl _

/-- Same-store equality retains both instances and the complete original
shared atom tree, including branches not visited by either selected input. -/
theorem same_avoids {h} (tree : ContractionTree .atom (h+2))
    (f : Occurrence (AtomEquality.Same.before tree d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort h 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let head : (AtomEquality.Same.before tree d).Edge := ⟨.compare,(0 : Fin 1)⟩
  obtain ⟨n,leftPath,_⟩ := AtomEquality.Same.resolves_left tree d
  have operand : StoreTrace.Operand (AtomEquality.Same.before tree d)
      (AtomEquality.Same.inputPort h 0) (.binary .atomEq) 0 (AtomEquality.Same.beforeStore tree d) n :=
    ⟨head,AtomEquality.Same.beforeLeft tree d,⟨rfl,List.mem_cons_self⟩,
      ⟨.internal (.inl (0 : Fin 5)),rfl,List.mem_cons_self⟩,leftPath⟩
  have mapped := StoreTrace.operand_map f.matchEmbedding operand
  change StoreTrace.Operand (C.expand L) (f.ports (AtomEquality.Same.inputPort h 0)) _ _ _ _ at mapped
  rw [attached] at mapped
  obtain ⟨_,store⟩ := store_operand_owner C cert heads (by intro eq; cases eq) mapped
  intro e
  apply ancestor_of_retained_not_hole C cert none closed f (b := AtomEquality.Same.beforeStore tree d) _ store
  obtain ⟨part,e⟩ := e
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact .step ⟨.internal (.inl (0 : Fin 5)),List.mem_cons_self,List.mem_cons_self⟩ (StoreTrace.ancestor leftPath.1)
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact StoreTrace.ancestor leftPath.1
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    obtain ⟨n,rightPath,_⟩ := AtomEquality.Same.resolves_right tree d
    exact StoreTrace.ancestor rightPath.1
  · obtain ⟨n,path⟩ := tree.reaches_root e
    have mapped : Trace (AtomEquality.Same.before tree d).Adjacent
        (AtomEquality.Same.beforeLeftTree tree d e) (AtomEquality.Same.beforeLeftTree tree d tree.root) n :=
      path.map (AtomEquality.Same.beforeLeftTree tree d) (fun p => by
        obtain ⟨w,target,source⟩ := p
        exact ⟨AtomEquality.Same.beforeLeftVertex tree d w,List.mem_map_of_mem target,List.mem_map_of_mem source⟩)
    have last : (AtomEquality.Same.before tree d).Adjacent
        (AtomEquality.Same.beforeLeftTree tree d tree.root) (AtomEquality.Same.beforeStore tree d) := by
      refine ⟨AtomEquality.Same.beforeLeftVertex tree d (.output 0),List.mem_map_of_mem tree.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
    exact BindingOverlap.trace_ancestor (Dereference.trace_snoc mapped last)
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact .refl _

/-- Distinct-store equality retains each complete original atom tree and
both actual stores. The store-inequality and contents interfaces are unchanged. -/
theorem different_avoids {n m} (tree : ContractionTree .atom (n+1)) (other : ContractionTree .atom (m+1))
    (f : Occurrence (AtomEquality.Different.before tree other d) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding := by
  let head : (AtomEquality.Different.before tree other d).Edge := ⟨.compare,(0 : Fin 1)⟩
  obtain ⟨k,leftPath,_⟩ := AtomEquality.Different.resolves_left tree other d
  obtain ⟨l,rightPath,_⟩ := AtomEquality.Different.resolves_right tree other d
  have leftOperand : StoreTrace.Operand (AtomEquality.Different.before tree other d)
      (AtomEquality.Different.inputPort n m 0) (.binary .atomEq) 0 (AtomEquality.Different.beforeStore tree other d) k :=
    ⟨head,AtomEquality.Different.beforeLeft tree other d,⟨rfl,List.mem_cons_self⟩,
      ⟨.internal (.inl (0 : Fin 6)),rfl,List.mem_cons_self⟩,leftPath⟩
  have rightOperand : StoreTrace.Operand (AtomEquality.Different.before tree other d)
      (AtomEquality.Different.inputPort n m 0) (.binary .atomEq) 1 (AtomEquality.Different.beforeStoreRight tree other d) l :=
    ⟨head,AtomEquality.Different.beforeRight tree other d,⟨rfl,List.mem_cons_self⟩,
      ⟨.internal (.inl (1 : Fin 6)),rfl,List.mem_cons_self⟩,rightPath⟩
  have leftMapped := StoreTrace.operand_map f.matchEmbedding leftOperand
  have rightMapped := StoreTrace.operand_map f.matchEmbedding rightOperand
  change StoreTrace.Operand (C.expand L) (f.ports (AtomEquality.Different.inputPort n m 0)) _ _ _ _ at leftMapped rightMapped
  rw [attached] at leftMapped rightMapped
  obtain ⟨_,leftStore⟩ := store_operand_owner C cert heads (by intro eq; cases eq) leftMapped
  obtain ⟨_,rightStore⟩ := store_operand_owner C cert heads (by intro eq; cases eq) rightMapped
  rintro ⟨part,e⟩
  cases part
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact ancestor_of_retained_not_hole C cert none closed f
      (.step ⟨.internal (.inl (0 : Fin 6)),List.mem_cons_self,List.mem_cons_self⟩
        (StoreTrace.ancestor leftPath.1)) leftStore
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact ancestor_of_retained_not_hole C cert none closed f (StoreTrace.ancestor leftPath.1) leftStore
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact ancestor_of_retained_not_hole C cert none closed f (StoreTrace.ancestor rightPath.1) rightStore
  · apply ancestor_of_retained_not_hole C cert none closed f (b := AtomEquality.Different.beforeStore tree other d) _ leftStore
    obtain ⟨k,path⟩ := tree.reaches_root e
    have mapped : Trace (AtomEquality.Different.before tree other d).Adjacent
        (AtomEquality.Different.beforeLeftTree tree other d e) (AtomEquality.Different.beforeLeftTree tree other d tree.root) k :=
      path.map (AtomEquality.Different.beforeLeftTree tree other d) (fun p => by
        obtain ⟨w,target,source⟩ := p
        exact ⟨AtomEquality.Different.beforeLeftVertex tree other d w,List.mem_map_of_mem target,List.mem_map_of_mem source⟩)
    have last : (AtomEquality.Different.before tree other d).Adjacent
        (AtomEquality.Different.beforeLeftTree tree other d tree.root) (AtomEquality.Different.beforeStore tree other d) := by
      refine ⟨AtomEquality.Different.beforeLeftVertex tree other d (.output 0),List.mem_map_of_mem tree.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
    exact BindingOverlap.trace_ancestor (Dereference.trace_snoc mapped last)
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact ancestor_of_retained_not_hole C cert none closed f (.refl _) leftStore
  · apply ancestor_of_retained_not_hole C cert none closed f (b := AtomEquality.Different.beforeStoreRight tree other d) _ rightStore
    obtain ⟨k,path⟩ := other.reaches_root e
    have mapped : Trace (AtomEquality.Different.before tree other d).Adjacent
        (AtomEquality.Different.beforeRightTree tree other d e) (AtomEquality.Different.beforeRightTree tree other d other.root) k :=
      path.map (AtomEquality.Different.beforeRightTree tree other d) (fun p => by
        obtain ⟨w,target,source⟩ := p
        exact ⟨AtomEquality.Different.beforeRightVertex tree other d w,List.mem_map_of_mem target,List.mem_map_of_mem source⟩)
    have last : (AtomEquality.Different.before tree other d).Adjacent
        (AtomEquality.Different.beforeRightTree tree other d other.root) (AtomEquality.Different.beforeStoreRight tree other d) := by
      refine ⟨AtomEquality.Different.beforeRightVertex tree other d (.output 0),List.mem_map_of_mem other.root_output,?_⟩
      change _ ∈ [_]; exact List.mem_cons_self
    exact BindingOverlap.trace_ancestor (Dereference.trace_snoc mapped last)
  · change Fin 1 at e; have eq : e = 0 := Subsingleton.elim _ _; subst e
    exact ancestor_of_retained_not_hole C cert none closed f (.refl _) rightStore

end Hypernets.Copying.LambdaEntryOverlap

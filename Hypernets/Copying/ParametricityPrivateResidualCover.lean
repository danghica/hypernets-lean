import Hypernets.Copying.ParametricityPrivateResidualNormal

/-! Every edge left by the private read is explicitly accounted for. The
normal form preserves the complete ordered residual term tree and cell. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead.ResidualNormal
open Graph Opening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

/-- The old read rule's primitive-frame presentation and original rule have
bijective edge carriers, even when the inverse is not definitionally simple. -/
theorem read_cover (b : Dereference.BeforeEdge)
    (e : (Dereference.Context.family (AtomResidual.spine.atDepth d) b).Edge) :
    ∃ a, (readOccurrence T d).edges a =
      (Dereference.Context.components (ready T d) (treeOccurrence T d)
        (reader T d) (instanceEdge T d) (store T d)
        (reader_label T d) (instance_label T d) (store_label T d) b).edges e := by
  let f := Dereference.Context.graphIso (d := d) AtomResidual.spine
  refine ⟨f.edges.toFun ⟨b,e⟩,?_⟩
  change (Dereference.Context.components _ _ _ _ _ _ _ _
    (f.edges.invFun (f.edges.toFun ⟨b,e⟩)).1).edges (f.edges.invFun (f.edges.toFun ⟨b,e⟩)).2 = _
  rw [f.edges.left_inv]

theorem tail_covers_reader : ∃ a, (tailOccurrence T d).edges a = reader T d := by
  obtain ⟨a,h⟩ := read_cover T d .reader (by cases d <;> exact (0 : Fin 1))
  cases d <;> exact ⟨⟨false,a⟩,h⟩

theorem tail_covers_instance : ∃ a, (tailOccurrence T d).edges a = instanceEdge T d := by
  obtain ⟨a,h⟩ := read_cover T d .inst (by cases d <;> exact (0 : Fin 1))
  cases d <;> exact ⟨⟨false,a⟩,h⟩

theorem tail_covers_atom (i : Fin 3) : ∃ a, (tailOccurrence T d).edges a = atomEdges T d i := by
  obtain ⟨a,h⟩ := read_cover T d .tree i
  cases d <;> exact ⟨⟨false,a⟩,h⟩

theorem tail_covers_store : ∃ a, (tailOccurrence T d).edges a = store T d := by
  obtain ⟨a,h⟩ := read_cover T d .store (by cases d <;> exact (0 : Fin 1))
  cases d <;> exact ⟨⟨false,a⟩,h⟩

/-- The ready private-cell graph consists precisely of the matched read,
the retained reference branch, and the two untouched weakening leaves. -/
theorem original_cover (e : (ready T d).Edge) :
    (∃ a, (tailOccurrence T d).edges a = e) ∨
    (∃ a, (original T d).edges a = e) ∨
    ∃ b a, (AtomResidual.oldWeak T d b).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨b,e⟩
    cases b
    · rcases e with ⟨b,e⟩
      cases b
      · change Fin 1 at e
        have zero : e=0 := Subsingleton.elim _ _
        subst e
        exact .inl (tail_covers_reader T _)
      · rcases e with ⟨b,e⟩
        cases b
        · rcases e with ⟨b,e⟩
          cases b
          · change Fin 1 at e
            have zero : e=0 := Subsingleton.elim _ _
            subst e
            exact .inl (tail_covers_instance T _)
          · exact .inr (.inl ⟨e,rfl⟩)
        · rcases e with ⟨b,e⟩
          cases b
          · exact Fin.elim0 e.1
          · rcases e with ⟨i,e⟩
            change Fin 1 at i
            have zero : i=0 := Subsingleton.elim _ _
            subst i
            change Fin 3 at e
            have options : e=0 ∨ e=1 ∨ e=2 := by omega
            rcases options with rfl | rfl | rfl
            · exact .inr (.inr ⟨false,(0 : Fin 1),rfl⟩)
            · exact .inl (tail_covers_atom T _ 1)
            · exact .inl (tail_covers_atom T _ 0)
    · rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨b,e⟩
        cases b
        · change Fin 2 at e
          have options : e=0 ∨ e=1 := by omega
          rcases options with rfl | rfl
          · exact .inr (.inr ⟨true,(0 : Fin 1),rfl⟩)
          · exact .inl (tail_covers_atom T _ 2)
        · change Fin 1 at e
          have zero : e=0 := Subsingleton.elim _ _
          subst e
          exact .inl (tail_covers_store T _)
      · change Fin 1 at e
        have zero : e=0 := Subsingleton.elim _ _
        subst e
        exact .inl ⟨⟨true,(0 : Fin 1)⟩,rfl⟩

/-- The actual computed cut keeps every unmatched old edge and exactly the
new returned numeral, residual atom tree, store and stored numeral. -/
theorem corrected_cover (e : (corrected T d).Edge) :
    (∃ a, (referenceOccurrence T d).edges a = e) ∨
    (∃ b a, (AtomResidual.weak T d b).edges a = e) ∨
    (∃ a, (AtomResidual.tree T d).edges a = e) ∨
    (∃ a, (numeralOccurrence T d).edges a = e) ∨
    ∃ a, (cellOccurrence T d).edges a = e := by
  cases e with
  | inl e =>
    rcases e with ⟨old,notHole⟩
    cases old with
    | none => exact False.elim (notHole rfl)
    | some old =>
      rcases old with ⟨old,unmatched⟩
      rcases original_cover T d old with ⟨a,h⟩ | ⟨a,h⟩ | ⟨b,a,h⟩
      · exact False.elim (unmatched a h)
      · subst old; exact .inl ⟨a,rfl⟩
      · subst old; exact .inr (.inl ⟨b,a,rfl⟩)
  | inr e =>
    cases d
    all_goals
      rcases e with ⟨b,e⟩
      cases b
      · exact .inr (.inr (.inr (.inl ⟨e,rfl⟩)))
      · rcases e with ⟨b,e⟩
        cases b
        · exact .inr (.inr (.inl ⟨e,rfl⟩))
        · exact .inr (.inr (.inr (.inr ⟨e,rfl⟩)))

theorem full_covers_weak (b : Bool) (e : ((ContractionTree.canonical .atom 0).atDepth d).Edge) :
    ∃ a, (AtomResidual.full T d).edges a = (AtomResidual.weak T d b).edges e := by
  let last := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) AtomResidual.firstTree 1 d
  cases b
  · let x := (ContractionTree.Graft.leftOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
      (AtomResidual.firstTree.atDepth d) 1).edges e
    refine ⟨last.edges.invFun x,?_⟩
    change (ContractionTree.Graft.Join.occurrence (AtomResidual.weak T d false) (AtomResidual.first T d) 1
      ((AtomResidual.weak_link T d false).trans (AtomResidual.first_input T d 1).symm)
      (AtomResidual.weak_first_disjoint T d)).edges (last.edges.toFun (last.edges.invFun x)) = _
    rw [last.edges.right_inv]
    exact ContractionTree.Graft.Join.left_edge _ _ _ _ _ e
  · let first := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) AtomResidual.localTree 2 d
    let y := (ContractionTree.Graft.leftOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
      (AtomResidual.localTree.atDepth d) 2).edges e
    let x := (ContractionTree.Graft.rightOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
      (AtomResidual.firstTree.atDepth d) 1).edges (first.edges.invFun y)
    refine ⟨last.edges.invFun x,?_⟩
    change (ContractionTree.Graft.Join.occurrence (AtomResidual.weak T d false) (AtomResidual.first T d) 1
      ((AtomResidual.weak_link T d false).trans (AtomResidual.first_input T d 1).symm)
      (AtomResidual.weak_first_disjoint T d)).edges (last.edges.toFun (last.edges.invFun x)) = _
    rw [last.edges.right_inv,ContractionTree.Graft.Join.right_edge]
    change (ContractionTree.Graft.Join.occurrence (AtomResidual.weak T d true) (AtomResidual.tree T d) 2
      (AtomResidual.weak_link T d true) (AtomResidual.weak_tree_disjoint T d true)).edges
      (first.edges.toFun (first.edges.invFun y)) = _
    rw [first.edges.right_inv]
    exact ContractionTree.Graft.Join.left_edge _ _ _ _ _ e

theorem full_covers_tree (e : (AtomResidual.localTree.atDepth d).Edge) :
    ∃ a, (AtomResidual.full T d).edges a = (AtomResidual.tree T d).edges e := by
  let first := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) AtomResidual.localTree 2 d
  let last := ContractionTree.graftInput_iso (ContractionTree.canonical .atom 0) AtomResidual.firstTree 1 d
  let y := (ContractionTree.Graft.rightOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
    (AtomResidual.localTree.atDepth d) 2).edges e
  let x := (ContractionTree.Graft.rightOccurrence ((ContractionTree.canonical .atom 0).atDepth d)
    (AtomResidual.firstTree.atDepth d) 1).edges (first.edges.invFun y)
  refine ⟨last.edges.invFun x,?_⟩
  change (ContractionTree.Graft.Join.occurrence (AtomResidual.weak T d false) (AtomResidual.first T d) 1
    ((AtomResidual.weak_link T d false).trans (AtomResidual.first_input T d 1).symm)
    (AtomResidual.weak_first_disjoint T d)).edges (last.edges.toFun (last.edges.invFun x)) = _
  rw [last.edges.right_inv,ContractionTree.Graft.Join.right_edge]
  change (ContractionTree.Graft.Join.occurrence (AtomResidual.weak T d true) (AtomResidual.tree T d) 2
    (AtomResidual.weak_link T d true) (AtomResidual.weak_tree_disjoint T d true)).edges
    (first.edges.toFun (first.edges.invFun y)) = _
  rw [first.edges.right_inv]
  exact ContractionTree.Graft.Join.right_edge _ _ _ _ _ e

theorem covers_reference (e : (reference T d).Edge) :
    ∃ a, (occurrence T d).edges a = (referenceOccurrence T d).edges e := by
  cases d <;> exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩

theorem covers_atom (e : (AtomResidual.fullTree.atDepth d).Edge) :
    ∃ a, (occurrence T d).edges a = (AtomResidual.full T d).edges e := by
  cases d <;> exact ⟨⟨true,⟨true,⟨false,e⟩⟩⟩,rfl⟩

theorem covers_numeral (e : (ReadTail.numeral d).Edge) :
    ∃ a, (occurrence T d).edges a = (numeralOccurrence T d).edges e := by
  cases d <;> exact ⟨⟨false,e⟩,rfl⟩

theorem covers_cell (e : (ReadTail.Normal.cell d).Edge) :
    ∃ a, (occurrence T d).edges a = (cellOccurrence T d).edges e := by
  cases d <;> exact ⟨⟨true,⟨true,⟨true,e⟩⟩⟩,rfl⟩

theorem cover (e : (corrected T d).Edge) : ∃ a, (occurrence T d).edges a = e := by
  rcases corrected_cover T d e with ⟨a,rfl⟩ | ⟨b,a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩ | ⟨a,rfl⟩
  · exact covers_reference T d a
  · obtain ⟨a,h⟩ := full_covers_weak T d b a
    obtain ⟨b,g⟩ := covers_atom T d a
    exact ⟨b,g.trans h⟩
  · obtain ⟨a,h⟩ := full_covers_tree T d a
    obtain ⟨b,g⟩ := covers_atom T d a
    exact ⟨b,g.trans h⟩
  · exact covers_numeral T d a
  · exact covers_cell T d a

theorem original_input (i : Fin (List.replicate n Wire.term).length) :
    (original T d).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp_all <;> omega⟩ := by
  change BoundarySerial.leftInsert _ _ ((readerCopy T d).ports
    (BoundarySerial.leftInsert _ _ (CopyRule.pairInsert (k := 0) (h := 1) T (primitiveNet d .instanceEdge) true (.input i)))) = _
  rw [CopyRule.pair_right_input,Combined.left_input]
  cases d with
  | zero =>
    change BoundarySerial.leftInsert
      (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge))) (tail 0)
      (Port.map Sum.inl ((ReaderPrefix.pattern 0 n (environmentInterface 0 1)).sourcePort true
        ⟨i.val+1,by change i.val+1 < (List.replicate (n+1) Wire.term).length; simpa using Nat.succ_lt_succ i.isLt⟩)) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,
      List.getElem_cons_succ,List.getElem_map,List.getElem_finRange,Port.map]
    exact Combined.left_input _ _ _
  | succ d =>
    change BoundarySerial.leftInsert
      (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet (d+1) .instanceEdge))) (tail (d+1))
      (Port.map Sum.inl ((ReaderPrefix.pattern (d+1) n (environmentInterface 0 1)).sourcePort true
        ⟨i.val+1,by change i.val+1 < (List.replicate (n+1) Wire.term).length; simpa using Nat.succ_lt_succ i.isLt⟩)) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,ReaderPrefix.frame,ReaderPrefix.source,Net.relabel,
      List.getElem_cons_succ,List.getElem_map,List.getElem_finRange,Port.map]
    exact Combined.left_input _ _ _

theorem reference_input (i : Fin (List.replicate n Wire.term).length) :
    (referenceOccurrence T d).ports (.input i) = .input ⟨i.val+1,by have := i.isLt; simp_all <;> omega⟩ :=
  (tailOccurrence T d).acrossCut_externalInput (original T d) (disjoint T d) _
    (.input i) _ (original_input T d i)

theorem numeral_input : (numeralOccurrence T d).ports (.input 0) = .input ⟨0,by simp⟩ := by
  change CompleteMatchCut.replacePort _ _ _ (.input ⟨0,by simp [Dereference.inputs]⟩) = _
  exact corrected_input T d

theorem input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (occurrence T d).ports (.input i) = .input i := by
  let B := Net.Tensor.boundary [Wire.term] (environmentInterface 0 0) (List.replicate n Wire.term) []
  let j : Fin ([Wire.term] ++ List.replicate n Wire.term).length := ⟨i.val,by have := i.isLt; simpa using this⟩
  have surj : ∃ x, B.inputs.toFun x = j := ⟨B.inputs.invFun j,B.inputs.right_inv j⟩
  obtain ⟨⟨b,k⟩,eq⟩ := surj
  have pos : (.input i : (normal T d).Vertex) = Port.cast (by simp [List.replicate_succ]) rfl
      (Net.Parallel.embed (Net.Tensor.family (ReadTail.numeral d) (stored T d)) B b (.input k)) := by
    change Port.input i = Port.input _
    apply congrArg Port.input
    apply Fin.ext
    exact (congrArg Fin.val eq).symm
  rw [pos]
  unfold occurrence
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]
  cases b
  · change Fin 1 at k
    have zero : k=0 := Subsingleton.elim _ _
    subst k
    have value : i.val=0 := (congrArg Fin.val eq).symm
    rw [numeral_input]
    exact congrArg Port.input (Fin.ext value.symm)
  · change (storedOccurrence T d).ports (.input k) = _
    unfold storedOccurrence
    rw [Occurrence.SerialJoin.occurrence_input,reference_input]
    apply congrArg Port.input
    apply Fin.ext
    have value : 1+k.val=i.val := congrArg Fin.val eq
    change k.val+1=i.val
    omega

/-- Exact graph reconstruction: the only active component is the returned
numeral; every other original term input still owns the retained private cell. -/
noncomputable def iso : DeepIso (normal T d) (corrected T d) :=
  (occurrence T d).iso_of_edge_surjective (input T d) (fun i => Fin.elim0 i) (cover T d)

end Hypernets.Copying.Parametricity.PrivateRead.ResidualNormal

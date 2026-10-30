import Hypernets.Copying.ParametricityPrivateAtomResidual

/-! Reassemble the private read's residual from its actual complementary
reference branch, returned numeral, and whole residual atom tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateRead.ResidualNormal
open Graph Opening
open BoxPullWeakening
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

abbrev reference := Serial.net (CopyRule.residual T d) (primitiveNet d .instanceEdge)

noncomputable def readerCopy : Occurrence (CopyRule.after (k := 0) (h := 1) T (primitiveNet d .instanceEdge))
    (ReaderPrefix.net (CopyRule.after (k := 0) (h := 1) T (primitiveNet d .instanceEdge))) := by
  cases d <;> exact Occurrence.expand (ReaderPrefix.pattern _ n (environmentInterface 0 1))
    (ReaderPrefix.filling (CopyRule.after (k := 0) (h := 1) T (primitiveNet _ .instanceEdge))) true

noncomputable def original : Occurrence (reference T d) (ready T d) :=
  (((RetainedCopy.copyComponent (k := 0) (h := 1) T (primitiveNet d .instanceEdge) true).comp
    (ReverseComponents.serialLeft _ _)).comp (readerCopy T d)).comp
    (ReverseComponents.serialLeft _ _)

theorem read_disjoint : ∀ e c, (readOccurrence T d).edges e ≠ (original T d).edges c := by
  intro e c
  let selected := Dereference.Context.occurrence (ready T d) (treeOccurrence T d)
    (reader T d) (instanceEdge T d) (store T d)
    (reader_label T d) (instance_label T d) (store_label T d)
    (.input ⟨0,by simp⟩) (argument T d) (atomPath T d 0) (atomPath T d 3) (storeValue T d)
    (reader_source T d) (reader_target T d) (instance_source T d) (instance_target T d)
    (store_source T d) (store_target T d) rfl rfl (fun i => .inr (.inl (atom_label T d i)))
  have all (x : (Dereference.Context.graph (AtomResidual.spine.atDepth d)).Edge) :
      selected.edges x ≠ (original T d).edges c := by
    rcases x with ⟨b,j⟩
    cases b <;> cases d
    all_goals
      intro eq
      simp only [selected,Dereference.Context.occurrence,Occurrence.ExpansionJoin.occurrence] at eq
    all_goals try
      change Fin 3 at j
      have options : j=0 ∨ j=1 ∨ j=2 := by omega
      rcases options with rfl | rfl | rfl
    all_goals
      solve
      | (have bad := congrArg Sigma.fst eq; cases bad)
      | (have bad := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2); cases bad)
      | (have bad := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2); cases bad)
      | (have bad := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj eq).2)).2)).2); cases bad)
  exact all ((Occurrence.ofIso (Dereference.Context.graphIso (d := d) AtomResidual.spine).symm).edges e)

theorem disjoint : ∀ e c, (tailOccurrence T d).edges e ≠ (original T d).edges c := by
  cases d <;> rintro ⟨b,e⟩ c eq <;> cases b
  all_goals solve
    | exact read_disjoint T _ e c eq
    | (have bad := congrArg Sigma.fst eq; cases bad)

noncomputable def referenceOccurrence : Occurrence (reference T d) (corrected T d) :=
  (tailOccurrence T d).acrossCut (original T d) (disjoint T d) _

noncomputable def numeralOccurrence : Occurrence (ReadTail.numeral d) (corrected T d) :=
  (RetainedCopy.targetCast
    (Occurrence.ParallelJoin.component
      (Net.Tensor.family (ReadTail.numeral d) (ReadTail.Normal.retainedCell AtomResidual.spine d))
      (Net.Tensor.boundary _ _ _ _) _ false)
    (by simp [Dereference.inputs]) (by simp [environmentInterface])).comp (AtomResidual.inserted T d)

noncomputable def cellOccurrence : Occurrence (ReadTail.Normal.cell d) (corrected T d) :=
  (ReverseComponents.serialRight _ _).comp (AtomResidual.localCell T d)

theorem reference_atom : (referenceOccurrence T d).ports (.output ⟨0,by decide⟩) =
    (AtomResidual.full T d).ports (.input ⟨0,by decide⟩) := by
  rw [AtomResidual.full_input,AtomResidual.tree_input]
  apply (tailOccurrence T d).acrossCut_replacement_input
  cases d <;> rfl

theorem atom_cell : (AtomResidual.full T d).ports (.output 0) =
    (cellOccurrence T d).ports (.input 0) := by
  rw [AtomResidual.full_output]
  exact congrArg (AtomResidual.localCell T d).ports
    (ReverseComponents.serial_boundary (AtomResidual.localTree.atDepth d) (ReadTail.Normal.cell d) 0)

theorem reference_labels : AllLabels (fun p => p ≠ .weakening .atom ∧ p ≠ .contraction .atom)
    (reference T d) := by
  apply Serial.allLabels_net
  · intro e
    rcases ((CopyRule.residualTree T).sharingTreeGraph d).labels e with eq | eq
    all_goals change LabelAll _ d (((CopyRule.residualTree T).atDepth d).edgeLabel e); rw [eq]; cases d <;> constructor <;> intro h <;> cases h
  · cases d <;> intro e <;> constructor <;> intro h <;> cases h

theorem reference_atom_disjoint : ∀ e c,
    (referenceOccurrence T d).edges e ≠ (AtomResidual.full T d).edges c := by
  intro e c eq
  have labels := (labelAll_equiv _ d ((referenceOccurrence T d).label e)).mp (reference_labels T d e)
  rcases (AtomResidual.fullTree.sharingTreeGraph d).labels c with old | old
  all_goals
    have target := (AtomResidual.full T d).matchEmbedding.primitive c _ old
    change (corrected T d).edgeLabel ((AtomResidual.full T d).edges c) = _ at target
    rw [eq,target] at labels
    have bad := (Dereference.label_primitive _ d _).mp labels
    first | exact bad.1 rfl | exact bad.2 rfl

theorem atom_cell_disjoint : ∀ e c,
    (AtomResidual.full T d).edges e ≠ (cellOccurrence T d).edges c := by
  intro e c eq
  have labels : AllLabels (fun p => p ≠ .weakening .atom ∧ p ≠ .contraction .atom)
      (ReadTail.Normal.cell d) := by
    apply Serial.allLabels_net
    all_goals cases d <;> intro e <;> constructor <;> intro h <;> cases h
  have label := (labelAll_equiv _ d ((cellOccurrence T d).label c)).mp (labels c)
  rcases (AtomResidual.fullTree.sharingTreeGraph d).labels e with old | old
  all_goals
    have target := (AtomResidual.full T d).matchEmbedding.primitive e _ old
    change (corrected T d).edgeLabel ((AtomResidual.full T d).edges e) = _ at target
    rw [← eq,target] at label
    have bad := (Dereference.label_primitive _ d _).mp label
    first | exact bad.1 rfl | exact bad.2 rfl

theorem reference_cell_disjoint : ∀ e c,
    (referenceOccurrence T d).edges e ≠ (cellOccurrence T d).edges c := by
  cases d <;> intro e c eq <;> cases eq

def atomCell := Serial.net (AtomResidual.fullTree.atDepth d) (ReadTail.Normal.cell d)

noncomputable def atomCellOccurrence : Occurrence (atomCell d) (corrected T d) :=
  Occurrence.SerialJoin.occurrence (AtomResidual.full T d) (cellOccurrence T d)
    (by intro i; change Fin 1 at i; have zero : i=0 := Subsingleton.elim _ _; subst i; exact atom_cell T d)
    (atom_cell_disjoint T d)

def stored := Serial.net (reference T d) (atomCell d)

noncomputable def storedOccurrence : Occurrence (stored T d) (corrected T d) :=
  Occurrence.SerialJoin.occurrence (referenceOccurrence T d) (atomCellOccurrence T d)
    (by
      intro i
      change Fin 1 at i
      have zero : i=⟨0,by decide⟩ := Subsingleton.elim _ _
      subst i
      unfold atomCellOccurrence
      rw [Occurrence.SerialJoin.occurrence_input]
      exact reference_atom T d)
    (by
      cases d <;> intro e c <;> rcases c with ⟨b,c⟩ <;> cases b
      all_goals first | exact reference_atom_disjoint T _ e c | exact reference_cell_disjoint T _ e c)

theorem numeral_reference_disjoint : ∀ e c,
    (numeralOccurrence T d).edges e ≠ (referenceOccurrence T d).edges c := by
  cases d <;> intro e c eq <;> cases eq

theorem numeral_atom_disjoint : ∀ e c,
    (numeralOccurrence T d).edges e ≠ (AtomResidual.full T d).edges c := by
  intro e c eq
  rcases (AtomResidual.fullTree.sharingTreeGraph d).labels c with label | label
  all_goals
    have old := (AtomResidual.full T d).matchEmbedding.primitive c _ label
    have fresh := (numeralOccurrence T d).matchEmbedding.primitive e (.operation (.const (.nat 1))) (by cases d <;> rfl)
    have bad := primitiveLabel_injective d
      (fresh.symm.trans ((congrArg (corrected T d).edgeLabel eq).trans old))
    cases bad

theorem numeral_cell_disjoint : ∀ e c,
    (numeralOccurrence T d).edges e ≠ (cellOccurrence T d).edges c := by
  cases d <;> intro e c eq
  all_goals
    have inner := Sum.inr.inj eq
    have bad := congrArg Sigma.fst inner
    cases bad

theorem numeral_stored_disjoint : ∀ e c,
    (numeralOccurrence T d).edges e ≠ (storedOccurrence T d).edges c := by
  cases d <;> intro e c <;> rcases c with ⟨b,c⟩ <;> cases b
  all_goals first
    | exact numeral_reference_disjoint T _ e c
    | (rcases c with ⟨b,c⟩; cases b
       · exact numeral_atom_disjoint T _ e c
       · exact numeral_cell_disjoint T _ e c)

def normal : Hypernet d (List.replicate (n+1) .term) [] :=
  (Net.Tensor.net (ReadTail.numeral d) (stored T d)).reboundary
    (by simp [List.replicate_succ]) rfl

noncomputable def occurrence : Occurrence (normal T d) (corrected T d) :=
  (Occurrence.ParallelJoin.occurrence (Net.Tensor.family (ReadTail.numeral d) (stored T d))
    (Net.Tensor.boundary _ _ _ _) ⟨[false,true],by intro b; cases b <;> simp⟩
    (fun b => by cases b; exact numeralOccurrence T d; exact storedOccurrence T d)
    (by
      intro a b ne e c
      cases a <;> cases b
      all_goals first
        | exact False.elim (ne rfl)
        | exact numeral_stored_disjoint T d e c
        | exact fun eq => numeral_stored_disjoint T d c e eq.symm)).reboundarySource
      (by simp [List.replicate_succ]) rfl

end Hypernets.Copying.Parametricity.PrivateRead.ResidualNormal

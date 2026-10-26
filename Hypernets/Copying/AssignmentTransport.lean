import Hypernets.Copying.AssignmentPreservation

/-! Carrier renaming and recursive padding for the actual assignment graphs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def before_congr {d h O} {T U : ContractionTree .atom (h+1)}
    {G H : Hypernet d [.term] O} (treeIso : T.net.Iso U.net) (valueIso : DeepIso G H) :
    DeepIso (before T G) (before U H) := by
  cases d <;> apply Net.ExpansionIso.iso
  all_goals
    intro e; cases e
    · exact DeepIso.refl _
    · exact DeepIso.refl _
    · exact Dereference.liftIso (Net.RelIso.ofIso (fun _ => rfl) treeIso) _
    · exact DeepIso.refl _
    · exact valueIso

def after_congr {d h O} {T U : ContractionTree .atom (h+1)}
    {G H : Hypernet d [.term] O} (treeIso : T.net.Iso U.net) (valueIso : DeepIso G H) :
    DeepIso (after T G) (after U H) := by
  cases d <;> apply Net.ExpansionIso.iso
  all_goals
    intro e; cases e
    · exact DeepIso.refl _
    · exact DeepIso.refl _
    · exact Dereference.liftIso (Net.RelIso.ofIso (fun _ => rfl) treeIso) _
    · exact DeepIso.refl _
    · exact valueIso
    · exact DeepIso.refl _
    · exact DeepIso.refl _

noncomputable def before_raise_graph {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Net.Iso (Padding.graph (before T G)) (before T (Padding.graph G)) := by
  cases d
  all_goals
    let vm : Bijection (Padding.graph (before T G)).Internal (before T (Padding.graph G)).Internal := {
        toFun := fun | .inl v => .inl v | .inr ⟨.assign,v⟩ => .inr ⟨.assign,v⟩ | .inr ⟨.inst,v⟩ => .inr ⟨.inst,v⟩ | .inr ⟨.tree,v⟩ => .inr ⟨.tree,v⟩ | .inr ⟨.store,v⟩ => .inr ⟨.store,v⟩ | .inr ⟨.value,v⟩ => .inr ⟨.value,v⟩ 
        invFun := fun | .inl v => .inl v | .inr ⟨.assign,v⟩ => .inr ⟨.assign,v⟩ | .inr ⟨.inst,v⟩ => .inr ⟨.inst,v⟩ | .inr ⟨.tree,v⟩ => .inr ⟨.tree,v⟩ | .inr ⟨.store,v⟩ => .inr ⟨.store,v⟩ | .inr ⟨.value,v⟩ => .inr ⟨.value,v⟩ 
        left_inv := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl
        right_inv := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl }
    have host (v : Port (Fin 4) (inputs h).length (outputs O).length) :
        Port.map vm.toFun (Net.Expansion.host (beforePattern _ h O) (beforeFill T G) v) =
          Net.Expansion.host (beforePattern _ h O) (beforeFill T (Padding.graph G)) v := by cases v <;> rfl
    exact {
      vertices := vm
      edges := {
        toFun := fun | ⟨.assign,f⟩ => ⟨.assign,f⟩ | ⟨.inst,f⟩ => ⟨.inst,f⟩ | ⟨.tree,f⟩ => ⟨.tree,f⟩ | ⟨.store,f⟩ => ⟨.store,f⟩ | ⟨.value,f⟩ => ⟨.value,f⟩
        invFun := fun | ⟨.assign,f⟩ => ⟨.assign,f⟩ | ⟨.inst,f⟩ => ⟨.inst,f⟩ | ⟨.tree,f⟩ => ⟨.tree,f⟩ | ⟨.store,f⟩ => ⟨.store,f⟩ | ⟨.value,f⟩ => ⟨.value,f⟩
        left_inv := by rintro ⟨e,f⟩; cases e <;> rfl
        right_inv := by rintro ⟨e,f⟩; cases e <;> rfl }
      internal_label := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl
      edge_label := by rintro ⟨e,f⟩; cases e <;> rfl
      source := by
        rintro ⟨e,f⟩; cases e
        · change (((beforeFill T G .assign).source f).map _).map _ = ((beforeFill T G .assign).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .inst).source f).map _).map _ = ((beforeFill T G .inst).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .tree).source f).map _).map _ = ((beforeFill T G .tree).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .store).source f).map _).map _ = ((beforeFill T G .store).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .value).source f).map _).map _ = ((beforeFill T G .value).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
      target := by
        rintro ⟨e,f⟩; cases e
        · change (((beforeFill T G .assign).target f).map _).map _ = ((beforeFill T G .assign).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .inst).target f).map _).map _ = ((beforeFill T G .inst).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .tree).target f).map _).map _ = ((beforeFill T G .tree).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .store).target f).map _).map _ = ((beforeFill T G .store).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((beforeFill T G .value).target f).map _).map _ = ((beforeFill T G .value).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
    }

noncomputable def before_raise {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    DeepIso (raise d (before T G)) (before T (raise d G)) := by
  simpa only [Padding.graph_eq_raise] using DeepIso.ofIso (before_raise_graph T G)

noncomputable def after_raise_graph {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    Net.Iso (Padding.graph (after T G)) (after T (Padding.graph G)) := by
  cases d
  all_goals
    let vm : Bijection (Padding.graph (after T G)).Internal (after T (Padding.graph G)).Internal := {
        toFun := fun | .inl v => .inl v | .inr ⟨.discardInstance,v⟩ => .inr ⟨.discardInstance,v⟩ | .inr ⟨.inst,v⟩ => .inr ⟨.inst,v⟩ | .inr ⟨.tree,v⟩ => .inr ⟨.tree,v⟩ | .inr ⟨.store,v⟩ => .inr ⟨.store,v⟩ | .inr ⟨.value,v⟩ => .inr ⟨.value,v⟩ | .inr ⟨.discardOld,v⟩ => .inr ⟨.discardOld,v⟩ | .inr ⟨.unit,v⟩ => .inr ⟨.unit,v⟩ 
        invFun := fun | .inl v => .inl v | .inr ⟨.discardInstance,v⟩ => .inr ⟨.discardInstance,v⟩ | .inr ⟨.inst,v⟩ => .inr ⟨.inst,v⟩ | .inr ⟨.tree,v⟩ => .inr ⟨.tree,v⟩ | .inr ⟨.store,v⟩ => .inr ⟨.store,v⟩ | .inr ⟨.value,v⟩ => .inr ⟨.value,v⟩ | .inr ⟨.discardOld,v⟩ => .inr ⟨.discardOld,v⟩ | .inr ⟨.unit,v⟩ => .inr ⟨.unit,v⟩ 
        left_inv := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl
        right_inv := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl }
    have host (v : Port (Fin 4) (inputs h).length (outputs O).length) :
        Port.map vm.toFun (Net.Expansion.host (afterPattern _ h O) (afterFill T G) v) =
          Net.Expansion.host (afterPattern _ h O) (afterFill T (Padding.graph G)) v := by cases v <;> rfl
    exact {
      vertices := vm
      edges := {
        toFun := fun | ⟨.discardInstance,f⟩ => ⟨.discardInstance,f⟩ | ⟨.inst,f⟩ => ⟨.inst,f⟩ | ⟨.tree,f⟩ => ⟨.tree,f⟩ | ⟨.store,f⟩ => ⟨.store,f⟩ | ⟨.value,f⟩ => ⟨.value,f⟩ | ⟨.discardOld,f⟩ => ⟨.discardOld,f⟩ | ⟨.unit,f⟩ => ⟨.unit,f⟩
        invFun := fun | ⟨.discardInstance,f⟩ => ⟨.discardInstance,f⟩ | ⟨.inst,f⟩ => ⟨.inst,f⟩ | ⟨.tree,f⟩ => ⟨.tree,f⟩ | ⟨.store,f⟩ => ⟨.store,f⟩ | ⟨.value,f⟩ => ⟨.value,f⟩ | ⟨.discardOld,f⟩ => ⟨.discardOld,f⟩ | ⟨.unit,f⟩ => ⟨.unit,f⟩
        left_inv := by rintro ⟨e,f⟩; cases e <;> rfl
        right_inv := by rintro ⟨e,f⟩; cases e <;> rfl }
      internal_label := by rintro (v | ⟨e,v⟩); rfl; cases e <;> rfl
      edge_label := by rintro ⟨e,f⟩; cases e <;> rfl
      source := by
        rintro ⟨e,f⟩; cases e
        · rfl
        · change (((afterFill T G .inst).source f).map _).map _ = ((afterFill T G .inst).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .tree).source f).map _).map _ = ((afterFill T G .tree).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .store).source f).map _).map _ = ((afterFill T G .store).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .value).source f).map _).map _ = ((afterFill T G .value).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · rfl
        · change (((afterFill T G .unit).source f).map _).map _ = ((afterFill T G .unit).source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
      target := by
        rintro ⟨e,f⟩; cases e
        · change (((afterFill T G .discardInstance).target f).map _).map _ = ((afterFill T G .discardInstance).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .inst).target f).map _).map _ = ((afterFill T G .inst).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .tree).target f).map _).map _ = ((afterFill T G .tree).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .store).target f).map _).map _ = ((afterFill T G .store).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .value).target f).map _).map _ = ((afterFill T G .value).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · change (((afterFill T G .discardOld).target f).map _).map _ = ((afterFill T G .discardOld).target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v
          · rfl
          · exact host _
          · exact host _
        · rfl
    }

noncomputable def after_raise {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    DeepIso (raise d (after T G)) (after T (raise d G)) := by
  simpa only [Padding.graph_eq_raise] using DeepIso.ofIso (after_raise_graph T G)

/-- Assignment pairs up to recursive representation renaming, retaining stability. -/
def UpToIso {d h O} (L R : Hypernet d (inputs h) (outputs O)) : Prop :=
  ∃ T G, Stable G ∧ Nonempty (DeepIso L (before T G)) ∧ Nonempty (DeepIso R (after T G))
theorem rule_upToIso {d h O} {L R : Hypernet d (inputs h) (outputs O)} (s : Rule L R) : UpToIso L R := by
  obtain ⟨T,G,stable,rfl,rfl⟩ := rule_iff.mp s
  exact ⟨T,G,stable,⟨DeepIso.refl _⟩,⟨DeepIso.refl _⟩⟩
theorem upToIso_raise {d h O} {L R : Hypernet d (inputs h) (outputs O)} (s : UpToIso L R) :
    UpToIso (raise d L) (raise d R) := by
  obtain ⟨T,G,stable,⟨f⟩,⟨g⟩⟩ := s
  exact ⟨T,raise d G,(Stable.raise_iff G).mpr stable,⟨(Padding.congr f).trans (before_raise T G)⟩,
    ⟨(Padding.congr g).trans (after_raise T G)⟩⟩
theorem upToIso_pad {d h O} {L R : Hypernet d (inputs h) (outputs O)} (s : UpToIso L R) (n : Nat) :
    UpToIso (Translation.pad d n L) (Translation.pad d n R) := by
  induction n with
  | zero => exact s
  | succ n ih => exact upToIso_raise ih
end Hypernets.Copying.Assignment

import Hypernets.Copying.TermWeakening
import Hypernets.Copying.OperationalContextualEquivalence

/-! Removing only genuinely empty forests from closed translation clauses.
Every equality below is an ordered recursive graph isomorphism. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ClosedTranslation
open Graph Opening

noncomputable def serial_empty {d I} (G : Hypernet d I []) (E : Hypernet d [] [])
    (empty : ∀ e : E.Edge, False) : DeepIso G (Serial.net G E) := by
  apply (BoxPullWeakening.ReverseComponents.serialLeft G E).iso_of_edge_surjective
  · intro i; exact Combined.left_input G E i
  · intro i; exact Fin.elim0 i
  · cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first | exact ⟨e,rfl⟩ | exact False.elim (empty e)

noncomputable def tensor_empty_right {d I O} (G : Hypernet d I O) (E : Hypernet d [] [])
    (empty : ∀ e : E.Edge, False) : DeepIso G
      (Translation.castInterfaces (List.append_nil I) (List.append_nil O) (Net.Tensor.net G E)) := by
  rw [BoxPullWeakening.cast_eq_reboundary]
  apply ((Occurrence.tensorComponent G E false).reboundaryTarget (List.append_nil I) (List.append_nil O)).iso_of_edge_surjective
  · intro i; exact congrArg Port.input (Fin.ext rfl)
  · intro i; exact congrArg Port.output (Fin.ext rfl)
  · cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first | exact ⟨e,rfl⟩ | exact False.elim (empty e)

noncomputable def tensor_empty_left {d I O} (E : Hypernet d [] []) (G : Hypernet d I O)
    (empty : ∀ e : E.Edge, False) : DeepIso G (Net.Tensor.net E G) := by
  apply (Occurrence.tensorComponent E G true).iso_of_edge_surjective
  · intro i; cases d <;> simp [Occurrence.tensorComponent,Occurrence.ParallelJoin.component,
      Net.Tensor.boundary,Net.Parallel.embed,Net.Tensor.ports,Net.Tensor.join]
  · intro i; cases d <;> simp [Occurrence.tensorComponent,Occurrence.ParallelJoin.component,
      Net.Tensor.boundary,Net.Parallel.embed,Net.Tensor.ports,Net.Tensor.join]
  · cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first | exact ⟨e,rfl⟩ | exact False.elim (empty e)

theorem distributor_empty (d m : Nat) (s : ShareSort) :
    ∀ e : (Distributor.atDepth s 0 m d).Edge, False := by
  cases d <;> intro e <;> exact Fin.elim0 e.1

theorem environment_empty (d m : Nat) :
    ∀ e : (Translation.environmentDistributor d 0 0 m).Edge, False := by
  cases d <;> rintro ⟨b,e⟩ <;> cases b <;> exact Fin.elim0 e.1

theorem singleUse_empty (d : Nat) : ∀ e : (Translation.singleUse d 0 0).Edge, False := by
  cases d <;> rintro ⟨b,e⟩ <;> cases b <;> exact Fin.elim0 e.1

noncomputable def constant (d : Nat) (c : Constant) :
    DeepIso (Translation.constant d 0 0 c) (primitiveNet d (.operation (.const c))) := by
  have f := tensor_empty_left (Distributor.atDepth .term 0 0 d)
    (primitiveNet d (.operation (.const c))) (distributor_empty d 0 .term)
  have g := tensor_empty_right (Net.Tensor.net (Distributor.atDepth .term 0 0 d)
    (primitiveNet d (.operation (.const c)))) (Distributor.atDepth .atom 0 0 d)
      (distributor_empty d 0 .atom)
  exact (f.trans g).symm

noncomputable def unary {d} (o : Unary) (G : Hypernet d [.term] []) :
    DeepIso (Translation.unary (k := 0) (h := 0) o G) (Serial.net (primitiveNet d (.operation (.unary o))) G) :=
  (serial_empty _ _ (singleUse_empty d)).symm

noncomputable def abstraction {d} (G : Hypernet d [.term] (environmentInterface 1 0)) :
    DeepIso (Translation.abstraction G) (Application.closure G) :=
  (serial_empty _ _ (singleUse_empty (d+1))).symm
noncomputable def pair {d} (G H : Hypernet d [.term] []) :
    DeepIso (Translation.pair (k := 0) (h := 0) G H) (Net.Tensor.net G H) := by
  rw [Weakening.Pair.original_pair]
  apply DeepIso.symm
  let f := Occurrence.ParallelJoin.occurrence (Net.Tensor.family G H)
    (Net.Tensor.boundary [Wire.term] [] [Wire.term] [])
    ⟨[false,true],by intro b; cases b <;> simp⟩
    (Weakening.Pair.component (k := 0) (h := 0) G H)
    (by intro a b ne e c eq; cases a <;> cases b
        · exact ne rfl
        · cases eq
        · cases eq
        · exact ne rfl)
  apply f.iso_of_edge_surjective
  · rintro ⟨i,hi⟩
    have bound : i < 2 := hi
    have split : i = 0 ∨ i = 1 := by omega
    rcases split with rfl | rfl <;> rfl
  · intro i; exact Fin.elim0 i
  · cases d <;> rintro ⟨b,e⟩ <;> cases b <;> exact ⟨⟨_,e⟩,rfl⟩

noncomputable def application {d} (G H : Hypernet d [.term] []) :
    DeepIso (Translation.application (k := 0) (h := 0) G H)
      (Serial.net (primitiveNet d (.operation .app)) (Net.Tensor.net G H)) :=
  (serial_empty _ _ (environment_empty d 2)).symm.trans
    (Serial.congr (DeepIso.refl _) (pair G H))
end Hypernets.Copying.ClosedTranslation

import Hypernets.Copying.AtomicResourceComplement

/-! Identity specializations of the injective atomic embeddings retain exactly
the original identity occurrence, including their ordered boundary action. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening

theorem occurrence_ext {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (f g : Occurrence G H) (ports : f.ports = g.ports) (edges : f.edges = g.edges) : f = g := by
  have internals : f.internals = g.internals := by
    funext v
    exact Port.internal.inj ((f.internal_map v).symm.trans ((congrFun ports (.internal v)).trans (g.internal_map v)))
  cases f; cases g
  cases ports; cases edges; cases internals
  rfl

theorem tensorMap_identity {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K) :
    (Occurrence.ofIso (DeepIso.refl G)).tensorMap (Occurrence.ofIso (DeepIso.refl H)) =
      Occurrence.ofIso (DeepIso.refl (Net.Tensor.net G H)) := by
  apply occurrence_ext
  · funext v
    cases v with
    | internal v => rcases v with ⟨b,v⟩; cases b <;> rfl
    | input i =>
      have eq := (Net.Tensor.ports I J).right_inv i
      generalize tag : (Net.Tensor.ports I J).invFun i = x at eq
      rcases x with ⟨b,x⟩
      cases b
      · have law := Occurrence.tensorMap_input_left (Occurrence.ofIso (DeepIso.refl G)) (Occurrence.ofIso (DeepIso.refl H)) x x rfl
        rw [show Net.Tensor.join I J ⟨false,x⟩ = i from eq] at law
        exact law
      · have law := Occurrence.tensorMap_input_right (Occurrence.ofIso (DeepIso.refl G)) (Occurrence.ofIso (DeepIso.refl H)) x x rfl
        rw [show Net.Tensor.join I J ⟨true,x⟩ = i from eq] at law
        exact law
    | output i =>
      have eq := (Net.Tensor.ports O K).right_inv i
      generalize tag : (Net.Tensor.ports O K).invFun i = x at eq
      rcases x with ⟨b,x⟩
      cases b
      · have law := Occurrence.tensorMap_output_left (Occurrence.ofIso (DeepIso.refl G)) (Occurrence.ofIso (DeepIso.refl H)) x x rfl
        rw [show Net.Tensor.join O K ⟨false,x⟩ = i from eq] at law
        exact law
      · have law := Occurrence.tensorMap_output_right (Occurrence.ofIso (DeepIso.refl G)) (Occurrence.ofIso (DeepIso.refl H)) x x rfl
        rw [show Net.Tensor.join O K ⟨true,x⟩ = i from eq] at law
        exact law
  · funext e; rcases e with ⟨b,e⟩; cases b <;> rfl

theorem serialPrefix_identity {d I J O} (P : Hypernet d I J) (G : Hypernet d J O)
    (inputs : ∀ i, (Occurrence.ofIso (DeepIso.refl G)).ports (.input i) = .input i) :
    (Occurrence.ofIso (DeepIso.refl G)).serialPrefix P inputs = Occurrence.ofIso (DeepIso.refl (Serial.net P G)) := by
  apply occurrence_ext
  · funext v
    cases v with
    | input i => exact Occurrence.serialPrefix_input P _ inputs i
    | output i => exact Occurrence.serialPrefix_output P _ inputs i i rfl
    | internal v =>
      cases d
      all_goals
        cases v with
        | inl i => exact CopyRule.serial_left_output P G i
        | inr v => rcases v with ⟨b,v⟩; cases b <;> rfl
  · cases d <;> funext e <;> rcases e with ⟨b,e⟩ <;> cases b <;> rfl

theorem forestEmbedding_id (s : ShareSort) (d n : Nat) (inj : Function.Injective (id : Fin n → Fin n)) :
    forestEmbedding s d id inj = Occurrence.ofIso (DeepIso.refl (Distributor.atDepth s n 0 d)) := by
  unfold forestEmbedding Occurrence.ofIso DeepIso.refl
  congr 1
  funext v
  cases v with
  | internal v => rfl
  | input i => exact Fin.elim0 i
  | output i => rfl

theorem rawEmbedding_id (s : ShareSort) (d : Nat) {n} (i : Fin n)
    (inj : Function.Injective (id : Fin n → Fin n)) :
    SelectedResource.rawEmbedding s d id inj i = Occurrence.ofIso (DeepIso.refl (SelectedResource.raw s d i)) := by
  have mapId : SelectedResource.mapOutput (id : Fin n → Fin n) = id := by funext v; cases v <;> rfl
  have sumId : Sum.map (id : Fin n → Fin n) (id : Unit → Unit) = id := by funext v; cases v <;> rfl
  unfold SelectedResource.rawEmbedding Occurrence.ofIso DeepIso.refl
  congr 1
  · funext v
    rw [mapId]
    change (SelectedResource.ports s d i).invFun ((SelectedResource.ports s d i).toFun v) = Port.map id v
    rw [Port.map_id_fun]
    exact (SelectedResource.ports s d i).left_inv v
  · funext v
    exact (SelectedResource.internal s d i).left_inv v
  · funext e
    rw [sumId]
    exact SelectedResource.edgeAt_index s d i e

theorem castIdentity {d I O J K} (G : Hypernet d I O) (hi : I = J) (ho : O = K) :
    (Occurrence.ofIso (DeepIso.refl G)).castInterfaces hi ho hi ho =
      Occurrence.ofIso (DeepIso.refl (Translation.castInterfaces hi ho G)) := by
  cases hi; cases ho; rfl

theorem selectedEmbedding_id (s : ShareSort) (d : Nat) {n} (i : Fin n)
    (inj : Function.Injective (id : Fin n → Fin n)) :
    SelectedResource.embedding s d id inj i = Occurrence.ofIso (DeepIso.refl (Translation.selectedResource d s i)) := by
  unfold SelectedResource.embedding
  rw [rawEmbedding_id,castIdentity]
  rfl
end Hypernets.Copying.Weakening.Atomic

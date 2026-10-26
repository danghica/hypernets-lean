import Hypernets.Copying.Application

/-! Micro-beta preserves ordered recursive representation changes and padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

def splice_congr {d F O} {B C : Hypernet d [.term] (.term :: F)}
    {G H : Hypernet d [.term] O} (f : DeepIso B C) (g : DeepIso G H) :
    DeepIso (splice B G) (splice C H) := by
  apply Net.ExpansionIso.iso
  intro b; cases b <;> cases d
  · exact f
  · exact f
  · exact g
  · exact g

def tensor_congr {d I O J K} {G H : Hypernet d I O} {U V : Hypernet d J K}
    (f : DeepIso G H) (g : DeepIso U V) : DeepIso (Net.Tensor.net G U) (Net.Tensor.net H V) :=
  Net.ParallelIso.iso (fun b => by cases b; exact f; exact g) _ _

def closure_congr {d k h} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : DeepIso B C) : DeepIso (closure B) (closure C) :=
  Serial.congr (DeepIso.refl _) (box_congr (Translation.castInterfaces_congr _ _ f))
def before_congr {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (f : DeepIso B C) (g : DeepIso G H) :
    DeepIso (before B G) (before C H) := Serial.congr (DeepIso.refl _) (tensor_congr (closure_congr f) g)
noncomputable def after_congr {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (f : DeepIso B C) (g : DeepIso G H) :
    DeepIso (after B G) (after C H) := splice_congr (Translation.castInterfaces_congr _ _ (Padding.congr f)) g

theorem renamed_rule {d k h O} {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (_f : DeepIso B C) (g : DeepIso G H) (stable : Stable G) :
    Rule (before C H) (after C H) := .beta C H (Stable.iso g stable)

noncomputable def splice_raise_graph {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    Net.Iso (Padding.graph (splice B G)) (splice (Padding.graph B) (Padding.graph G)) := by
  cases d
  all_goals
    let vm : Bijection (Padding.graph (splice B G)).Internal (splice (Padding.graph B) (Padding.graph G)).Internal := {
      toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
      invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
      left_inv := by rintro (v | ⟨b,v⟩); rfl; cases b <;> rfl
      right_inv := by rintro (v | ⟨b,v⟩); rfl; cases b <;> rfl }
    have host (v : Port (Fin 1) 1 (F ++ O).length) :
        Port.map vm.toFun (Net.Expansion.host (splicePattern _ F O) (spliceFilling B G) v) =
          Net.Expansion.host (splicePattern _ F O) (spliceFilling (Padding.graph B) (Padding.graph G)) v := by cases v <;> rfl
    exact {
      vertices := vm
      edges := {
        toFun := fun | ⟨false,e⟩ => ⟨false,e⟩ | ⟨true,e⟩ => ⟨true,e⟩
        invFun := fun | ⟨false,e⟩ => ⟨false,e⟩ | ⟨true,e⟩ => ⟨true,e⟩
        left_inv := by rintro ⟨b,e⟩; cases b <;> rfl
        right_inv := by rintro ⟨b,e⟩; cases b <;> rfl }
      internal_label := by rintro (v | ⟨b,v⟩); rfl; cases b <;> rfl
      edge_label := by rintro ⟨b,e⟩; cases b <;> rfl
      source := by
        rintro ⟨b,e⟩; cases b
        · change ((B.source e).map _).map _ = (B.source e).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _; cases v
          · rfl
          · exact host _
          · exact host _
        · change ((G.source e).map _).map _ = (G.source e).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _; cases v
          · rfl
          · exact host _
          · exact host _
      target := by
        rintro ⟨b,e⟩; cases b
        · change ((B.target e).map _).map _ = (B.target e).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _; cases v
          · rfl
          · exact host _
          · exact host _
        · change ((G.target e).map _).map _ = (G.target e).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _; cases v
          · rfl
          · exact host _
          · exact host _
    }

noncomputable def splice_raise {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) :
    DeepIso (raise d (splice B G)) (splice (raise d B) (raise d G)) := by
  simpa only [Padding.graph_eq_raise] using DeepIso.ofIso (splice_raise_graph B G)

noncomputable def closure_raise {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    DeepIso (raise (d+1) (closure B)) (closure (raise d B)) := by
  simpa only [closure,Padding.primitive,Padding.lambdaBox] using
    Padding.serial (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox B)

noncomputable def before_raise {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    DeepIso (raise (d+1) (before B G)) (before (raise d B) (raise (d+1) G)) := by
  have f := (Padding.serial (primitiveNet (d+1) (.operation .app)) (Net.Tensor.net (closure B) G))
  rw [Padding.primitive,Padding.tensor] at f
  exact f.trans (Serial.congr (DeepIso.refl _) (tensor_congr (closure_raise B) (DeepIso.refl _)))

theorem openBody_raise {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    raise (d+1) (openBody B) = openBody (raise d B) := by
  simp only [openBody,Padding.castInterfaces]

noncomputable def after_raise {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    DeepIso (raise (d+1) (after B G)) (after (raise d B) (raise (d+1) G)) := by
  simpa only [after,openBody_raise] using splice_raise (openBody B) G

theorem raised_rule {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
    Rule (before (raise d B) (raise (d+1) G)) (after (raise d B) (raise (d+1) G)) :=
  .beta _ _ ((Stable.raise_iff G).mpr stable)
/-- Representation closure keeps the actual body and stable-argument witnesses. -/
def UpToIso {d k h O} (L R : Hypernet (d+1) [.term] (environmentInterface k h ++ O)) : Prop :=
  ∃ B G, Stable G ∧ Nonempty (DeepIso L (before (d := d) (k := k) (h := h) B G)) ∧
    Nonempty (DeepIso R (after B G))

theorem rule_upToIso {d k h O} {L R : Hypernet (d+1) [.term] (environmentInterface k h ++ O)}
    (step : Rule L R) : UpToIso L R := by
  obtain ⟨B,G,stable,rfl,rfl⟩ := rule_iff.mp step
  exact ⟨B,G,stable,⟨DeepIso.refl _⟩,⟨DeepIso.refl _⟩⟩

theorem upToIso_congr {d k h O} {L R L' R' : Hypernet (d+1) [.term] (environmentInterface k h ++ O)}
    (f : DeepIso L L') (g : DeepIso R R') (step : UpToIso L R) : UpToIso L' R' := by
  obtain ⟨B,G,stable,⟨a⟩,⟨b⟩⟩ := step
  exact ⟨B,G,stable,⟨f.symm.trans a⟩,⟨g.symm.trans b⟩⟩

/-- Padding transports the body, argument, stability and both rule sides together. -/
theorem upToIso_raise {d k h O} {L R : Hypernet (d+1) [.term] (environmentInterface k h ++ O)}
    (step : UpToIso L R) : UpToIso (raise (d+1) L) (raise (d+1) R) := by
  obtain ⟨B,G,stable,⟨a⟩,⟨b⟩⟩ := step
  exact ⟨raise d B,raise (d+1) G,(Stable.raise_iff G).mpr stable,
    ⟨(Padding.congr a).trans (before_raise B G)⟩,
    ⟨(Padding.congr b).trans (after_raise B G)⟩⟩
end Hypernets.Copying.Application

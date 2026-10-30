import Hypernets.Copying.CopyingMergeRewrite
import Hypernets.Copying.CopyingRetainedContext
import Hypernets.Copying.ContractionTreeGraftSerial

/-! Factor the actual upstream tree out of the active branch of a copying
reduct. The retained branch and both ordered resource blocks are unchanged. -/
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Hypernets.Copying.CopyingRemoteRight.Pair
open Graph Opening
open ContractionTree
variable {d a b k h : Nat}
    (P : Hypernet d (List.replicate a .term) [.term])
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h))

abbrev target := CopyingMerge.pair (Serial.net P H) B
noncomputable def upstream :=
  (BoxPullWeakening.ReverseComponents.serialLeft P H).comp
    (CopyingMerge.pairComponent (Serial.net P H) B false)
noncomputable def active :=
  (Occurrence.serialRight P H).comp (CopyingMerge.pairComponent (Serial.net P H) B false)
noncomputable def retained := CopyingMerge.pairComponent (Serial.net P H) B true

noncomputable def branches (side : Bool) : Occurrence (Net.Tensor.family H B side) (target P H B) := by
  cases side
  · exact active P H B
  · exact retained P H B

theorem branches_disjoint : ∀ x y, x ≠ y → ∀ e f,
    (branches P H B x).edges e ≠ (branches P H B y).edges f := by
  cases d
  all_goals
    intro x y ne e f eq
    cases x <;> cases y
    · exact ne rfl
    · cases eq
    · cases eq
    · exact ne rfl

noncomputable def joined : Occurrence (CopyingRetainedContext.copies H B) (target P H B) :=
  (Occurrence.ParallelJoin.occurrence (Net.Tensor.family H B) (CopyRule.pairBoundary b k h)
    ⟨[false,true],by intro side; cases side <;> simp⟩ (branches P H B) (branches_disjoint P H B)).reboundarySource
      (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])

def insert (side : Bool) (v : (Net.Tensor.family H B side).Vertex) :
    (CopyingRetainedContext.copies H B).Vertex :=
  Port.cast (by simp [List.replicate_succ]) (by simp [environmentInterface,Nat.mul_two])
    (Net.Parallel.embed (Net.Tensor.family H B) (CopyRule.pairBoundary b k h) side v)

theorem joined_insert (side : Bool) (v : (Net.Tensor.family H B side).Vertex) :
    (joined P H B).ports (insert H B side v) = (branches P H B side).ports v := by
  unfold joined insert
  rw [Occurrence.reboundarySource_ports,Occurrence.ParallelJoin.occurrence_embed]

theorem joined_zero : (joined P H B).ports (.input ⟨0,by simp⟩) = (active P H B).ports (.input 0) := by
  have eq : insert H B false (.input (0 : Fin 1)) = .input ⟨0,by simp⟩ := congrArg Port.input (Fin.ext rfl)
  simpa only [eq,branches] using joined_insert P H B false (.input (0 : Fin 1))

theorem joined_other (i : Fin (List.replicate b Wire.term).length) :
    (joined P H B).ports (.input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩) =
      (retained P H B).ports (.input i) := by
  have eq : insert H B true (.input i) = .input ⟨i.val+1,by have := i.isLt; simp at *; omega⟩ := by
    apply congrArg Port.input
    apply Fin.ext
    change 1+i.val = i.val+1
    omega
  simpa only [eq,branches] using joined_insert P H B true (.input i)

noncomputable def components (e : (Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).Edge) :
    Occurrence (Graft.filling (s := .term) P (CopyingRetainedContext.copies H B) 0 e) (target P H B) := by
  cases d <;> cases e
  all_goals first | exact upstream P H B | exact joined P H B

noncomputable def host : (Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).Vertex → (target P H B).Vertex
  | .input i => .input i
  | .output i => .output i
  | .internal _ => (active P H B).ports (.input 0)

theorem branches_output (side : Bool) (i : Fin (environmentInterface k h).length) :
    (branches P H B side).ports (.output (by cases side <;> exact i)) =
      .output (PairBoundary.index side i) := by
  cases side with
  | false =>
    change (CopyingMerge.pairComponent (Serial.net P H) B false).ports
      (BoundarySerial.rightInsert P H (.output i)) = _
    rw [Application.right_serial_output]
    rfl
  | true => rfl

theorem joined_output (i : Fin (environmentInterface (k*2) (h*2)).length) :
    (joined P H B).ports (.output i) = .output i := by
  obtain ⟨side,j,rfl⟩ := PairBoundary.index_surjective i
  have eq : insert H B side (.output (by cases side <;> exact j)) =
      .output (PairBoundary.index side j) := by cases side <;> rfl
  rw [← eq,joined_insert,branches_output]

theorem input (e : (Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).Edge)
    (i : Fin ((alphabet d).signature.input ((Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).edgeLabel e)).length) :
    (components P H B e).ports (.input i) = host P H B
      ((Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).sourcePort e i) := by
  cases d
  all_goals
    cases e
    · change (CopyingMerge.pairComponent (Serial.net P H) B false).ports
        (BoundarySerial.leftInsert P H (.input i)) = _
      rw [Combined.left_input]
      simp only [Net.sourcePort,Graft.pattern,Graft.frame,Graft.sources,Net.relabel,
        List.getElem_map,List.getElem_finRange,Graft.upstream,host]
      exact congrArg Port.input (Fin.ext rfl)
    · change Fin (List.replicate (b+1) Wire.term).length at i
      change (joined P H B).ports (.input i) = _
      by_cases zero : i.val = 0
      · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
        subst i
        rw [joined_zero]
        simp only [Net.sourcePort,Graft.pattern,Graft.frame,Graft.sources,Net.relabel,
          List.getElem_map,List.getElem_finRange,Fin.cast,Fin.val_zero]
        change (active P H B).ports (.input 0) = host P H B
          (Graft.downstream .term a b (environmentInterface (k*2) (h*2)) (0 : Fin (b+1)) (0 : Fin (b+1)))
        rw [Graft.downstream_selected]
        rfl
      · let j : Fin (List.replicate b Wire.term).length := ⟨i.val-1,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩
        have eq : i = ⟨j.val+1,by have := j.isLt; simp only [List.length_replicate] at *; omega⟩ := Fin.ext (by simp [j]; omega)
        rw [eq,joined_other]
        simp only [Net.sourcePort,Graft.pattern,Graft.frame,Graft.sources,Net.relabel,
          List.getElem_map,List.getElem_finRange,Fin.cast,Fin.val_mk]
        unfold Graft.downstream
        simp only [Fin.val_zero]
        split
        · rename_i impossible
          have bad := congrArg Fin.val impossible
          simp only [Fin.val_mk,Fin.val_zero] at bad
          omega
        · change (CopyingMerge.pairComponent (Serial.net P H) B true).ports (.input j) = .input _
          apply congrArg Port.input
          apply Fin.ext
          simp only [CopyingMerge.pairComponent,CopyingMerge.boundary,Port.cast,
            Net.Parallel.embed,Net.Tensor.ports,Net.Tensor.join,List.length_replicate,Fin.val_mk,Fin.val_cast]
          simp only [Nat.not_lt_zero,↓reduceIte,Nat.add_sub_cancel]

theorem output (e : (Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).Edge)
    (i : Fin ((alphabet d).signature.output ((Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).edgeLabel e)).length) :
    (components P H B e).ports (.output i) = host P H B
      ((Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d).targetPort e i) := by
  cases d
  all_goals
    cases e
    · change Fin 1 at i
      have zero : i = 0 := Subsingleton.elim _ _
      subst i
      change (CopyingMerge.pairComponent (Serial.net P H) B false).ports
        (BoundarySerial.leftInsert P H (.output 0)) =
        (CopyingMerge.pairComponent (Serial.net P H) B false).ports
          (BoundarySerial.rightInsert P H (.input 0))
      rfl
    · change (joined P H B).ports (.output i) = _
      rw [joined_output]
      simp only [Net.targetPort,Graft.pattern,Graft.frame,Graft.targets,Net.relabel,
        List.getElem_map,List.getElem_finRange,Fin.cast,host]
      rfl

theorem disjoint : ∀ e f, e ≠ f → ∀ x y,
    (components P H B e).edges x ≠ (components P H B f).edges y := by
  cases d
  all_goals
    intro e f ne x y eq
    cases e <;> cases f
    · exact ne rfl
    · rcases y with ⟨side,y⟩
      cases side <;> cases eq
    · rcases x with ⟨side,x⟩
      cases side <;> cases eq
    · exact ne rfl

noncomputable def occurrence :
    Occurrence (Graft.net (s := .term) P (CopyingRetainedContext.copies H B) 0) (target P H B) :=
  Occurrence.ExpansionJoin.occurrence
    (Graft.pattern .term a b (environmentInterface (k*2) (h*2)) 0 d)
    (Graft.filling (s := .term) P (CopyingRetainedContext.copies H B) 0)
    (components P H B) (host P H B) (input P H B) (output P H B) (disjoint P H B)

theorem cover : Function.Surjective (occurrence P H B).edges := by
  cases d
  all_goals
    rintro ⟨side,e⟩
    cases side
    · rcases e with ⟨side,e⟩
      cases side
      · exact ⟨⟨false,e⟩,rfl⟩
      · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Moving the actual upstream graph into the first parallel branch preserves
every edge and fixes every external input and resource output. -/
noncomputable def iso : DeepIso
    (Graft.net (s := .term) P (CopyingRetainedContext.copies H B) 0)
    (CopyingMerge.pair (Serial.net P H) B) :=
  (occurrence P H B).iso_of_edge_surjective (fun _ => rfl) (fun _ => rfl) (cover P H B)

end Hypernets.Copying.CopyingRemoteRight.Pair

namespace Hypernets.Copying.CopyingRemoteRight
open Graph Opening Combined ContractionTree

/-- Pull the actual upstream graph into the active branch while retaining
all original output distributors and every remaining input. -/
noncomputable def factorIso {d a b k h : Nat}
    (P : Hypernet d (List.replicate a .term) [.term])
    (H : Hypernet d [.term] (environmentInterface k h))
    (B : Hypernet d (List.replicate b .term) (environmentInterface k h)) :
    DeepIso (Graft.net (s := .term) P (CopyingRetainedContext.after H B) 0)
      (CopyingMerge.net (Serial.net P H) B) :=
  (Graft.SerialRight.iso (s := .term) P (CopyingRetainedContext.copies H B)
    (Translation.environmentDistributor d k h 2) 0).trans
      (Serial.congr (Pair.iso P H B) (DeepIso.refl _))

/-- The actual right successor of the distinguished-input remote overlap. -/
def after {d a b k h : Nat} (P : ContractionTree .term (a+1))
    (T : ContractionTree .term (b+1))
    (H : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d (List.replicate (a+1+b) .term) (environmentInterface k h) :=
  CopyingMerge.net (CopyRule.after P H) (Serial.net (CopyRule.residual T d) H)

/-- One original Figure 17 rewrite occurs upstream of the shallow copying
component, with the token returned at the same original ordered input zero. -/
theorem rewrite {d a b k h : Nat} (P : ContractionTree .term (a+1))
    (T : ContractionTree .term (b+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable H) :
    Rewrite (Graft.net (s := .term) (P.atDepth d) (CopyRule.after T H) 0)
      (.input ⟨0,by simp only [List.length_replicate]; omega⟩) (after P T H) (.input ⟨0,by simp only [List.length_replicate]; omega⟩) := by
  have actual := CopyingMerge.left_rewrite (Serial.net (CopyRule.residual T d) H)
    (⟨0,by simp⟩ : Fin (List.replicate (a+1) Wire.term).length)
    ⟨0,by simp⟩ (.local (.copy P H copyable))
  exact actual.rename (factorIso (P.atDepth d) H (Serial.net (CopyRule.residual T d) H)).symm (DeepIso.refl _)

end Hypernets.Copying.CopyingRemoteRight

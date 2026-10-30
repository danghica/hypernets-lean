import Hypernets.Copying.ParametricityCopyContext
import Hypernets.Copying.OccurrenceTensorBoundary
import Hypernets.Copying.OccurrenceCoverIso
import Hypernets.Copying.OccurrenceBoundaryTarget

/-! Pull the residual copying-input context outside an arbitrary untouched
family. The external order remains active, remaining upstream inputs, family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyExtension
open Graph Opening
variable {d a n : Nat} {J K : List Wire}
    (P : Hypernet d (List.replicate a .term) [.term])
    (G : Hypernet d (List.replicate 2 .term) J)
    (R : Hypernet d (List.replicate n .term) K)

abbrev target : Hypernet d (List.replicate (a+(n+1)) .term) (J++K) :=
  (Net.Tensor.net (CopyContext.net (b := 0) P G) R).reboundary
    (by rw [List.replicate_append_replicate]; congr 1; omega) rfl
abbrev whole : Hypernet d (List.replicate ((n+1)+1) .term) (J++K) :=
  (Net.Tensor.net G R).reboundary (by rw [List.replicate_append_replicate]; congr 1; omega) rfl

noncomputable def left : Occurrence (CopyContext.net (b := 0) P G) (target P G R) :=
  (BoxPullWeakening.ReverseComponents.tensorLeft _ R).reboundaryTarget _ rfl
noncomputable def right : Occurrence R (target P G R) :=
  (BoxPullWeakening.ReverseComponents.tensorRight (CopyContext.net (b := 0) P G) R).reboundaryTarget _ rfl
noncomputable def upstream : Occurrence P (target P G R) := (CopyContext.upstream P G).comp (left P G R)
noncomputable def selected : Occurrence G (target P G R) := (CopyContext.family P G).comp (left P G R)

theorem selected_disjoint : ∀ e f, (selected P G R).edges e ≠ (right P G R).edges f := by
  intro e f eq; cases eq

noncomputable def family : Occurrence (whole G R) (target P G R) :=
  (BoxPullWeakening.ReverseComponents.tensorJoin (selected P G R) (right P G R)
    (selected_disjoint P G R)).reboundarySource _ rfl

theorem family_first (i : Fin 2) :
    (family P G R).ports (.input ⟨i.val,by simp; omega⟩) = (selected P G R).ports (.input i) := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P G R) (right P G R) (selected_disjoint P G R)).ports
    ((BoxPullWeakening.ReverseComponents.tensorLeft G R).ports (.input i)) = _
  exact Occurrence.tensorJoin_left _ _ _ _

theorem family_rest (i : Fin (List.replicate n Wire.term).length) :
    (family P G R).ports (.input ⟨2+i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩) =
      (right P G R).ports (.input i) := by
  change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P G R) (right P G R) (selected_disjoint P G R)).ports
    ((BoxPullWeakening.ReverseComponents.tensorRight G R).ports (.input i)) = _
  exact Occurrence.tensorJoin_right _ _ _ _

theorem link : (upstream P G R).ports (.output 0) = (family P G R).ports (.input ⟨1,by simp⟩) := by
  have eq := family_first P G R (1 : Fin 2)
  rw [show (⟨1,by simp⟩ : Fin (List.replicate (n+1+1) Wire.term).length) = ⟨(1 : Fin 2).val,by simp⟩ from rfl,eq]
  exact congrArg (left P G R).ports (CopyContext.retained_input P G).symm

theorem disjoint : ∀ e f, (upstream P G R).edges e ≠ (family P G R).edges f := by
  cases d <;> intro e f eq
  all_goals
    rcases f with ⟨side,f⟩; cases side
    · have same := congrArg Sigma.fst (eq_of_heq (Sigma.mk.inj eq).2)
      cases same
    · cases eq

noncomputable def raw : Occurrence
    (ContractionTree.Graft.net (s := .term) (b := n+1) P (whole G R) 1) (target P G R) :=
  ContractionTree.Graft.Join.occurrence (upstream P G R) (family P G R) 1
    (by simpa only [Fin.val_one] using link P G R) (disjoint P G R)

theorem upstream_input (i : Fin (List.replicate a Wire.term).length) :
    (upstream P G R).ports (.input i) = .input ⟨i.val+1,by
      have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  change (left P G R).ports ((CopyContext.upstream P G).ports (.input i)) = _
  rw [CopyContext.upstream_input]
  rfl

theorem family_active : (family P G R).ports (.input ⟨0,by simp⟩) = .input ⟨0,by simp <;> omega⟩ := by
  rw [show (⟨0,by simp⟩ : Fin (List.replicate (n+1+1) Wire.term).length) = ⟨(0 : Fin 2).val,by simp⟩ from rfl,family_first]
  change (left P G R).ports ((CopyContext.family P G).ports (.input ⟨0,by simp⟩)) = _
  rw [CopyContext.active_input]
  rfl

theorem family_other (i : Fin n) :
    (family P G R).ports (.input ⟨i.val+2,by simp <;> omega⟩) = .input ⟨a+i.val+1,by simp <;> omega⟩ := by
  have eq := family_rest P G R (⟨i.val,by simp⟩ : Fin (List.replicate n Wire.term).length)
  have idx : (⟨i.val+2,by simp <;> omega⟩ : Fin (List.replicate (n+1+1) Wire.term).length) =
      ⟨2+i.val,by simp <;> omega⟩ := Fin.ext (by change i.val+2=2+i.val; omega)
  rw [idx,eq]
  exact congrArg Port.input (Fin.ext (by
    change (List.replicate (a+1) Wire.term).length+i.val = a+i.val+1
    simp only [List.length_replicate]; omega))

theorem family_output (i : Fin (J++K).length) :
    (family P G R).ports (.output i) = .output i := by
  let x := Net.Tensor.split J K i
  have eq := Net.Tensor.join_split J K i
  change Net.Tensor.join J K x = i at eq
  rcases x with ⟨side,j⟩
  cases side
  · change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P G R) (right P G R) (selected_disjoint P G R)).ports (.output i) = _
    have represented : (BoxPullWeakening.ReverseComponents.tensorLeft G R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,Occurrence.tensorJoin_left]
    change (left P G R).ports ((CopyContext.family P G).ports (.output j)) = _
    rw [CopyContext.family_output]
    exact congrArg Port.output eq
  · change (BoxPullWeakening.ReverseComponents.tensorJoin (selected P G R) (right P G R) (selected_disjoint P G R)).ports (.output i) = _
    have represented : (BoxPullWeakening.ReverseComponents.tensorRight G R).ports (.output j) = .output i := congrArg Port.output eq
    rw [← represented,Occurrence.tensorJoin_right]
    exact congrArg Port.output eq

theorem raw_input (i : Fin (List.replicate (a+(n+1)) Wire.term).length) :
    (raw P G R).ports (.input i) = .input ((CopyContext.rotation a n).bijection.toFun i) := by
  by_cases before : i.val < a
  · let j : Fin (List.replicate a Wire.term).length := ⟨i.val,by simpa using before⟩
    have eq : ContractionTree.Graft.leftInsert (s := .term) (b := n+1) P (whole G R) 1 (.input j) = .input i := by
      rw [ContractionTree.Graft.left_input]; rfl
    rw [← eq]
    change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
    rw [ContractionTree.Graft.Join.left_port,upstream_input]
    simp only [CopyContext.rotation,CopyContext.forwardIndex,before,↓reduceIte]
    rfl
  · by_cases same : i.val = a
    · have eq : ContractionTree.Graft.rightInsert (s := .term) (b := n+1) P (whole G R) 1 (.input ⟨0,by simp⟩) = .input i := by
        rw [ContractionTree.Graft.right_input]
        simp only [ContractionTree.Graft.downstream]
        have no : (⟨0,by omega⟩ : Fin (n+1+1)) ≠ 1 := by intro eq; have := congrArg Fin.val eq; simp at this
        simp only [no,↓reduceDIte,Fin.val_one,Nat.zero_lt_succ,↓reduceIte,Nat.add_zero,Port.map]
        exact congrArg Port.input (Fin.ext same.symm)
      rw [← eq]
      change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
      rw [ContractionTree.Graft.Join.right_port,family_active]
      simp [CopyContext.rotation,CopyContext.forwardIndex,same]
    · let j : Fin n := ⟨i.val-a-1,by have := i.isLt; simp only [List.length_replicate] at this; omega⟩
      have val : a+j.val+1 = i.val := by dsimp [j]; omega
      have eq : ContractionTree.Graft.rightInsert (s := .term) (b := n+1) P (whole G R) 1
          (.input ⟨j.val+2,by simp <;> omega⟩) = .input i := by
        rw [ContractionTree.Graft.right_input]
        have no : (⟨j.val+2,by omega⟩ : Fin (n+1+1)) ≠ 1 := by
          intro eq; have := congrArg Fin.val eq; simp only [Fin.val_one] at this; omega
        simp only [ContractionTree.Graft.downstream,no,↓reduceDIte,Fin.val_one]
        have later : ¬ j.val+2 < 1 := by omega
        simp only [later,↓reduceIte,Port.map]
        apply congrArg Port.input
        apply Fin.ext
        change a+(j.val+2-1) = i.val
        omega
      rw [← eq]
      change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
      rw [ContractionTree.Graft.Join.right_port,family_other]
      simp only [CopyContext.rotation,CopyContext.forwardIndex,before,same,↓reduceIte]
      exact congrArg Port.input (Fin.ext val)

theorem raw_output (i : Fin (J++K).length) : (raw P G R).ports (.output i) = .output i := by
  rw [← ContractionTree.Graft.right_output (s := .term) (b := n+1) P (whole G R) (1 : Fin (n+1+1)) i]
  change (ContractionTree.Graft.Join.occurrence _ _ _ _ _).ports _ = _
  rw [ContractionTree.Graft.Join.right_port,family_output]

noncomputable def occurrence : Occurrence (CopyContext.net P (whole G R)) (target P G R) :=
  (CopyingDouble.Symmetry.backward _ (CopyContext.rotation a n)).comp (raw P G R)

theorem input (i : Fin (List.replicate (a+(n+1)) Wire.term).length) :
    (occurrence P G R).ports (.input i) = .input i := by
  change (raw P G R).ports (.input ((CopyContext.rotation a n).bijection.invFun i)) = _
  rw [raw_input,(CopyContext.rotation a n).bijection.right_inv]

theorem output (i : Fin (J++K).length) :
    (occurrence P G R).ports (.output i) = .output i := raw_output P G R i

theorem cover : Function.Surjective (occurrence P G R).edges := by
  cases d
  all_goals
    rintro ⟨side,e⟩; cases side
    · rcases e with ⟨side,e⟩; cases side
      · exact ⟨⟨false,e⟩,rfl⟩
      · exact ⟨⟨true,⟨false,e⟩⟩,rfl⟩
    · exact ⟨⟨true,⟨true,e⟩⟩,rfl⟩

/-- Exact tensor extension of the residual-input context. No permutation of
external inputs is hidden in this graph isomorphism. -/
noncomputable def iso : DeepIso (CopyContext.net P (whole G R)) (target P G R) :=
  (occurrence P G R).iso_of_edge_surjective (input P G R) (output P G R) (cover P G R)

end Hypernets.Copying.Parametricity.CopyExtension

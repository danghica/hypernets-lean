import Hypernets.Copying.ResourceBoundaryAction

/-! Exact resource actions for all original atomic translation clauses. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph EnvironmentPermutation

theorem selected_outputIndex (d : Nat) (s : ShareSort) {n}
    (π : Bijection (Fin n) (Fin n)) (i : Fin n) (j : Fin (List.replicate n s.wire).length) :
    (selectedResource_rename d s π i).outputs.toFun j =
      ⟨(π.toFun ⟨j.val,by simpa using j.isLt⟩).val,by simp⟩ := by
  have law := selectedResource_rename_output d s π i ⟨j.val,by simpa using j.isLt⟩
  rw [BoundaryIso.map_output] at law
  exact Port.output.inj law

theorem variableTerm_action (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k))
    (α : Bijection (Fin h) (Fin h)) (i : Fin k) : ResourceAction ρ α (variableTerm_rename d ρ α i) where
  term j := by
    have law := (selectedResource_rename d .term ρ i).tensor_output_left (Distributor.boundaryIso .atom 0 d α)
      ⟨j.val,by simp⟩
    rw [selected_outputIndex] at law
    have hh := BoundaryIso.castInterfaces_output
      (show [.term] ++ List.replicate (h*0) Wire.atom = [.term] by simp) rfl
      (show [.term] ++ List.replicate (h*0) Wire.atom = [.term] by simp) rfl _ _ _ law
    simpa only [variableTerm_rename,id,Fin.cast,Net.Tensor.join,termIndex] using hh
  atom a := by
    have law := (selectedResource_rename d .term ρ i).tensor_output_right (Distributor.boundaryIso .atom 0 d α)
      ⟨a.val,by simp⟩
    rw [Distributor.outputIndex_eq] at law
    have hh := BoundaryIso.castInterfaces_output
      (show [.term] ++ List.replicate (h*0) Wire.atom = [.term] by simp) rfl
      (show [.term] ++ List.replicate (h*0) Wire.atom = [.term] by simp) rfl _ _ _ law
    simpa only [variableTerm_rename,id,Fin.cast,Net.Tensor.join,List.length_replicate,atomIndex] using hh
end Hypernets.Copying.Translation

namespace Hypernets.Copying.InstancePrefix
open Graph
/-- The original instance prefix leaves the operand's output permutation intact. -/
theorem iso_output {d O K} {G : Hypernet d [.atom] O} {H : Hypernet d [.atom] K}
    (f : BoundaryIso G H) (i : Fin O.length) :
    (iso f).ports.toFun (.output i) = .output (f.outputs.toFun i) := by
  have law := lift_embed f (.output i)
  rw [f.map_output] at law
  cases d <;> exact law
end Hypernets.Copying.InstancePrefix

namespace Hypernets.Copying.Translation
open Graph EnvironmentPermutation

theorem atom_action (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k))
    (α : Bijection (Fin h) (Fin h)) (a : Fin h) : ResourceAction ρ α (atom_rename d ρ α a) where
  term i := by
    have law := (Distributor.boundaryIso .term 0 d ρ).tensor_output_left
      (InstancePrefix.iso (selectedResource_rename d .atom α a)) ⟨i.val,by simp⟩
    rw [Distributor.outputIndex_eq] at law
    have hh := BoundaryIso.castInterfaces_output
      (show List.replicate (k*0) Wire.term ++ [.term] = [.term] by simp) rfl
      (show List.replicate (k*0) Wire.term ++ [.term] = [.term] by simp) rfl _ _ _ law
    simpa only [atom_rename,id,Fin.cast,Net.Tensor.join,termIndex] using hh
  atom j := by
    have law := (Distributor.boundaryIso .term 0 d ρ).tensor_output_right
      (InstancePrefix.iso (selectedResource_rename d .atom α a)) ⟨j.val,by simp⟩
    have act := InstancePrefix.iso_output (selectedResource_rename d .atom α a) ⟨j.val,by simp⟩
    rw [BoundaryIso.map_output] at act
    have actIndex : (InstancePrefix.iso (selectedResource_rename d .atom α a)).outputs.toFun ⟨j.val,by simp⟩ = _ := Port.output.inj act
    rw [actIndex,selected_outputIndex] at law
    have hh := BoundaryIso.castInterfaces_output
      (show List.replicate (k*0) Wire.term ++ [.term] = [.term] by simp) rfl
      (show List.replicate (k*0) Wire.term ++ [.term] = [.term] by simp) rfl _ _ _ law
    simpa only [atom_rename,id,Fin.cast,Net.Tensor.join,List.length_replicate,atomIndex] using hh

theorem constant_action (d : Nat) {k h} (ρ : Bijection (Fin k) (Fin k))
    (α : Bijection (Fin h) (Fin h)) (c : Constant) : ResourceAction ρ α (constant_rename d ρ α c) where
  term i := by
    let f := (Distributor.boundaryIso .term 0 d ρ).tensor (BoundaryIso.refl (primitiveNet d (.operation (.const c))))
    let g := Distributor.boundaryIso .atom 0 d α
    have inner := (Distributor.boundaryIso .term 0 d ρ).tensor_output_left (BoundaryIso.refl (primitiveNet d (.operation (.const c)))) ⟨i.val,by simp⟩
    rw [Distributor.outputIndex_eq] at inner
    change f.ports.toFun (.output _) = .output _ at inner
    rw [f.map_output] at inner
    have law := f.tensor_output_left g (Net.Tensor.join (List.replicate k Wire.term) [] ⟨false,⟨i.val,by simpa [Net.Tensor.interfaces] using i.isLt⟩⟩)
    have innerIndex : f.outputs.toFun (Net.Tensor.join (List.replicate k Wire.term) [] ⟨false,⟨i.val,by simpa [Net.Tensor.interfaces] using i.isLt⟩⟩) =
      Net.Tensor.join (List.replicate k Wire.term) [] ⟨false,⟨(ρ.toFun i).val,by simpa [Net.Tensor.interfaces] using (ρ.toFun i).isLt⟩⟩ := Port.output.inj inner
    rw [innerIndex] at law
    have hh := BoundaryIso.castInterfaces_output
      (show (List.replicate (k*0) Wire.term ++ [.term]) ++ List.replicate (h*0) Wire.atom = [.term] by simp)
      (show (List.replicate k Wire.term ++ []) ++ List.replicate h Wire.atom = environmentInterface k h by simp [environmentInterface])
      (show (List.replicate (k*0) Wire.term ++ [.term]) ++ List.replicate (h*0) Wire.atom = [.term] by simp)
      (show (List.replicate k Wire.term ++ []) ++ List.replicate h Wire.atom = environmentInterface k h by simp [environmentInterface])
      (f.tensor g) _ _ law
    simpa only [constant_rename,id,f,g,Net.Tensor.join,Fin.cast,termIndex] using hh
  atom a := by
    let f := (Distributor.boundaryIso .term 0 d ρ).tensor (BoundaryIso.refl (primitiveNet d (.operation (.const c))))
    let g := Distributor.boundaryIso .atom 0 d α
    have law := f.tensor_output_right g ⟨a.val,by simp⟩
    rw [Distributor.outputIndex_eq] at law
    have hh := BoundaryIso.castInterfaces_output
      (show (List.replicate (k*0) Wire.term ++ [.term]) ++ List.replicate (h*0) Wire.atom = [.term] by simp)
      (show (List.replicate k Wire.term ++ []) ++ List.replicate h Wire.atom = environmentInterface k h by simp [environmentInterface])
      (show (List.replicate (k*0) Wire.term ++ [.term]) ++ List.replicate (h*0) Wire.atom = [.term] by simp)
      (show (List.replicate k Wire.term ++ []) ++ List.replicate h Wire.atom = environmentInterface k h by simp [environmentInterface])
      (f.tensor g) _ _ law
    simpa only [constant_rename,id,primitiveSignature,Operation.outputs,f,g,Net.Tensor.join,List.length_append,List.length_nil,Nat.add_zero,List.length_replicate,Fin.cast,atomIndex] using hh
end Hypernets.Copying.Translation

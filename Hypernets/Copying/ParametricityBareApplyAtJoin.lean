import Hypernets.Copying.ParametricityBareApplyAt
import Hypernets.Copying.ParametricityBareApplyJoinLaws

/-! Complete original components assemble an application at any original
family index. The other family inputs retain their original relative order. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt.Join
open Graph Opening
variable {d n I O} (G : Hypernet d (List.replicate (n+1) .term) [])
    {H : Hypernet d I O} (a : Occurrence (primitiveNet d (.operation .app)) H)
    (f : Occurrence G H) (j : Fin (n+1))

noncomputable def selectedFamily : Occurrence (selected G j) H :=
  (Occurrence.ofBoundaryIso (CopyingInputPermutation.iso G (order j).symm).symm).comp f

theorem selectedFamily_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (selectedFamily G f j).ports (.input i) = f.ports (.input ((order j).bijection.toFun i)) := rfl

variable (link : a.ports (.output (0 : Fin 2)) = f.ports (.input ⟨j.val,by simp⟩))
    (disjoint : ∀ e x, a.edges e ≠ f.edges x)

noncomputable def occurrence : Occurrence (net G j) H :=
  BareApplyFirst.Join.occurrence (selected G j) a (selectedFamily G f j) link disjoint

theorem input_zero : (occurrence G a f j link disjoint).ports (.input ⟨0,by simp⟩) =
    a.ports (.input (0 : Fin 1)) := rfl

theorem input_succ (i : Fin n) :
    (occurrence G a f j link disjoint).ports (.input ⟨i.val+1,by simp⟩) =
      f.ports (.input ((order j).bijection.toFun ⟨i.val+1,by simp⟩)) :=
  BareApplyFirst.Join.input_succ _ _ _ _ _ i

theorem output : (occurrence G a f j link disjoint).ports (.output 0) =
    a.ports (.output (1 : Fin 2)) := rfl

theorem head_port (v : (primitiveNet d (.operation .app)).Vertex) :
    (occurrence G a f j link disjoint).ports ((head G j).ports v) = a.ports v :=
  BareApplyFirst.Join.head_port _ _ _ _ _ v

theorem family_port (v : G.Vertex) :
    (occurrence G a f j link disjoint).ports ((family G j).ports v) = f.ports v := by
  change (BareApplyFirst.Join.occurrence _ _ _ _ _).ports
    ((BareApplyFirst.family (selected G j)).ports
      ((CopyingInputPermutation.iso G (order j).symm).ports.toFun v)) = _
  rw [BareApplyFirst.Join.family_port]
  change f.ports ((CopyingInputPermutation.iso G (order j).symm).ports.invFun
    ((CopyingInputPermutation.iso G (order j).symm).ports.toFun v)) = _
  rw [Bijection.left_inv]

theorem head_edge (e : (primitiveNet d (.operation .app)).Edge) :
    (occurrence G a f j link disjoint).edges ((head G j).edges e) = a.edges e := by cases d <;> rfl

theorem family_edge (e : G.Edge) :
    (occurrence G a f j link disjoint).edges ((family G j).edges e) = f.edges e := by cases d <;> rfl

end Hypernets.Copying.Parametricity.BareApplyAt.Join

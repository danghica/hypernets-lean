import Hypernets.Copying.ParametricityBareApplyAtJoin
import Hypernets.Copying.OccurrenceBoundaryCoverIso

/-! Transport the original selected-family application through a recorded
family boundary action. The active application input and callback output stay
fixed; all other inputs follow the original family permutation with the
selected position deleted on both sides. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyAt.Boundary
open Graph Opening
variable {d n} {G H : Hypernet d (List.replicate (n+1) .term) []}
    (f : BoundaryIso G H)

def image (i : Fin (n+1)) : Fin (n+1) :=
  ⟨(f.inputs.toFun ⟨i.val,by simp⟩).val,by simpa using (f.inputs.toFun ⟨i.val,by simp⟩).isLt⟩

variable (j : Fin (n+1))
noncomputable def original : Occurrence G (net H (image f j)) :=
  (Occurrence.ofBoundaryIso f).comp (family H (image f j))

theorem link : (head H (image f j)).ports (.output (0 : Fin 2)) =
    (original f j).ports (.input ⟨j.val,by simp⟩) := by
  change _ = (family H (image f j)).ports (f.ports.toFun (.input _))
  rw [f.map_input]
  exact head_function H (image f j)

theorem disjoint : ∀ e x, (head H (image f j)).edges e ≠ (original f j).edges x := by
  cases d <;> intro e x eq <;> cases congrArg Sigma.fst eq

noncomputable def occurrence : Occurrence (net G j) (net H (image f j)) :=
  Join.occurrence G (head H (image f j)) (original f j) j (link f j) (disjoint f j)

/-- The active input is fixed; the remaining action deletes the selected
position before and after the actual original family permutation. -/
def action (i : Fin (List.replicate (n+1) Wire.term).length) :=
  if i.val=0 then i else (order (image f j)).bijection.invFun
    (f.inputs.toFun ((order j).bijection.toFun i))

theorem input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (occurrence f j).ports (.input i) = .input (action f j i) := by
  have bound : i.val<n+1 := by simpa using i.isLt
  by_cases zero : i.val=0
  · have eq : i=⟨0,by simp⟩ := Fin.ext zero
    subst i
    rw [action,ite_eq_left rfl]
    exact head_input H (image f j)
  · let r : Fin n := ⟨i.val-1,by omega⟩
    have eq : i=⟨r.val+1,by simp⟩ := Fin.ext (by dsimp [r];omega)
    rw [action,ite_eq_right zero,eq]
    unfold occurrence
    rw [Join.input_succ]
    change (family H (image f j)).ports (f.ports.toFun (.input _)) = _
    rw [f.map_input]
    apply family_unselected
    intro bad
    have eq : (order j).bijection.toFun ⟨r.val+1,by simp⟩ = ⟨j.val,by simp⟩ := f.inputs.injective bad
    have same := (order j).bijection.injective (eq.trans (order_zero j).symm)
    have values := congrArg Fin.val same
    change r.val+1=0 at values
    omega

theorem output (i : Fin [Wire.term].length) :
    (occurrence f j).ports (.output i) = .output i := by
  change Fin 1 at i
  have eq : i=(0 : Fin 1) := Subsingleton.elim _ _
  subst i
  exact head_argument H (image f j)

theorem cover : Function.Surjective (occurrence f j).edges := by
  cases d
  all_goals
    rintro ⟨b,e⟩
    cases b
    · exact ⟨⟨false,e⟩,rfl⟩
    · refine ⟨⟨true,f.edges.invFun e⟩,?_⟩
      exact congrArg (fun x => (family H (image f j)).edges x) (f.edges.right_inv e)

/-- Full recursive labels and complete edge coverage give the required
original-graph boundary isomorphism, with no semantic premise. -/
noncomputable def iso : BoundaryIso (net G j) (net H (image f j)) :=
  (occurrence f j).boundaryIso_of_edge_surjective
    (by intro i;rw [input];trivial) (by intro i;rw [output];trivial) (cover f j)

theorem iso_input (i : Fin (List.replicate (n+1) Wire.term).length) :
    (iso f j).inputs.toFun i = action f j i := by
  have h := (iso f j).map_input i
  change (occurrence f j).ports (.input i) = .input ((iso f j).inputs.toFun i) at h
  exact Port.input.inj (h.symm.trans (input f j i))

theorem active : (iso f j).inputs.toFun ⟨0,by simp⟩ = ⟨0,by simp⟩ := by
  rw [iso_input]
  rfl

theorem iso_output (i : Fin [Wire.term].length) : (iso f j).outputs.toFun i = i := by
  have h := (iso f j).map_output i
  change (occurrence f j).ports (.output i) = .output ((iso f j).outputs.toFun i) at h
  exact Port.output.inj (h.symm.trans (output f j i))

omit j in
theorem image_congr {G' H' : Hypernet d (List.replicate (n+1) .term) []}
    (g : BoundaryIso G' H') (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i)
    (i : Fin (n+1)) : image f i = image g i := by
  apply Fin.ext
  exact congrArg (fun x : Fin (List.replicate (n+1) Wire.term).length => x.val) (same ⟨i.val,by simp⟩)

/-- The exact common family action produces the same application-context
input action on both sides, including the selected active position. -/
theorem same_inputs {G' H' : Hypernet d (List.replicate (n+1) .term) []}
    (g : BoundaryIso G' H') (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    ∀ i, (iso f j).inputs.toFun i = (iso g j).inputs.toFun i := by
  intro i
  rw [iso_input,iso_input]
  simp only [action,image_congr f g same,same]

end Hypernets.Copying.Parametricity.BareApplyAt.Boundary

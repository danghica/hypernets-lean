import Hypernets.Copying.ContractionTreeGraftOccurrence
import Hypernets.Copying.BoundaryOccurrence
import Hypernets.Copying.OccurrenceBoundaryCoverIso

/-! A downstream boundary isomorphism transports a literal input graft.
Every upstream input remains fixed; unselected downstream inputs follow the
recorded permutation with the selected position removed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft.BoundaryRight
open Graph Opening
variable {d a b : Nat} {s : ShareSort} {O : List Wire}
    (P : Hypernet d (List.replicate a s.wire) [s.wire])
    {G H : Hypernet d (List.replicate (b+1) s.wire) O} (f : BoundaryIso G H)

/-- The actual image of a downstream input, with only its length equality exposed. -/
def image (i : Fin (b+1)) : Fin (b+1) :=
  ⟨(f.inputs.toFun ⟨i.val,by simp⟩).val,by
    have h := (f.inputs.toFun ⟨i.val,by simp⟩).isLt
    simpa only [List.length_replicate] using h⟩

theorem image_injective : Function.Injective (image f) := by
  intro i j eq
  have values := congrArg (fun x : Fin (b+1) => x.val) eq
  change (f.inputs.toFun ⟨i.val,by simp⟩).val =
      (f.inputs.toFun ⟨j.val,by simp⟩).val at values
  have h := f.inputs.injective (Fin.ext values)
  exact Fin.ext (congrArg (fun x : Fin (List.replicate (b+1) s.wire).length => x.val) h)

/-- The ordered input remaining after deleting the selected downstream input. -/
def remaining (j i : Fin (b+1)) (ne : i ≠ j) :
    Fin (List.replicate (a+b) s.wire).length :=
  ⟨a + if i.val<j.val then i.val else i.val-1,by
    simp only [List.length_replicate]
    have h := i.isLt
    have k := j.isLt
    have different : i.val ≠ j.val := fun eq => ne (Fin.ext eq)
    split <;> omega⟩

theorem right_unselected (j i : Fin (b+1)) (ne : i ≠ j) :
    rightInsert P G j (.input ⟨i.val,by simp⟩) = .input (remaining (s := s) (a := a) j i ne) := by
  rw [right_input]
  change Port.map Sum.inl (downstream s a b O j i) = _
  simp only [downstream,ne,↓reduceDIte]
  rfl

variable (j : Fin (b+1))
noncomputable def left : Occurrence P (net P H (image f j)) := leftOccurrence P H (image f j)
noncomputable def right : Occurrence G (net P H (image f j)) :=
  (Occurrence.ofBoundaryIso f).comp (rightOccurrence P H (image f j))

theorem left_ports (v : P.Vertex) :
    (left P f j).ports v = leftInsert P H (image f j) v := leftOccurrence_ports _ _ _ _

theorem right_ports (v : G.Vertex) :
    (right P f j).ports v = rightInsert P H (image f j) (f.ports.toFun v) := by
  change (rightOccurrence P H (image f j)).ports ((Occurrence.ofBoundaryIso f).ports v) = _
  rw [rightOccurrence_ports]
  rfl

theorem link : (left P f j).ports (.output 0) =
    (right P f j).ports (.input ⟨j.val,by simp⟩) := by
  rw [left_ports,right_ports]
  rw [f.map_input]
  exact (selected_input P H (image f j)).symm

theorem disjoint : ∀ e c, (left P f j).edges e ≠ (right P f j).edges c := by
  cases d <;> intro e c eq <;> cases eq

/-- Both complete original components are retained, with the selected
attachment transported by the actual downstream input bijection. -/
noncomputable def occurrence : Occurrence (net P G j) (net P H (image f j)) :=
  Join.occurrence (left P f j) (right P f j) j (link P f j) (disjoint P f j)

theorem upstream_port (i : Fin (List.replicate a s.wire).length) :
    (occurrence P f j).ports (.input ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at *;omega⟩) =
      .input ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at *;omega⟩ := by
  rw [← left_input P G j i]
  unfold occurrence
  rw [Join.left_port]
  rw [left_ports]
  exact left_input P H (image f j) i

theorem downstream_port (i : Fin (b+1)) (ne : i ≠ j) :
    (occurrence P f j).ports (.input (remaining (s := s) (a := a) j i ne)) =
      .input (remaining (s := s) (a := a) (image f j) (image f i)
        (fun eq => ne (image_injective f eq))) := by
  rw [← right_unselected P j i ne]
  unfold occurrence
  rw [Join.right_port]
  rw [right_ports]
  rw [f.map_input]
  exact right_unselected P (image f j) (image f i) (fun eq => ne (image_injective f eq))

theorem output_port (i : Fin O.length) :
    (occurrence P f j).ports (.output i) = .output (f.outputs.toFun i) := by
  rw [← right_output P G j i]
  unfold occurrence
  rw [Join.right_port]
  rw [right_ports]
  rw [f.map_output,right_output]
  rfl

theorem inputs : ∀ i, ((occurrence P f j).ports (.input i)).IsInput := by
  intro i
  rcases input_covered s a b O j i with ⟨x,eq⟩ | ⟨x,eq⟩
  · have index : (⟨x.val,by simp;omega⟩ : Fin (List.replicate (a+b) s.wire).length) = i := Port.input.inj eq
    rw [← index,upstream_port P f j ⟨x.val,by simp⟩]
    trivial
  · have ne : x ≠ j := by
      intro same
      subst x
      rw [downstream_selected] at eq
      cases eq
    have index : remaining (s := s) (a := a) j x ne = i := by
      apply Port.input.inj (Internal := Fin 1) (outputs := O.length)
      simpa only [downstream,ne,↓reduceDIte,remaining] using eq
    rw [← index,downstream_port]
    trivial

theorem cover : Function.Surjective (occurrence P f j).edges := by
  cases d
  all_goals
    rintro ⟨side,e⟩
    cases side
    · exact ⟨⟨false,e⟩,rfl⟩
    · refine ⟨⟨true,f.edges.invFun e⟩,?_⟩
      exact congrArg (fun x => (rightOccurrence P H (image f j)).edges x) (f.edges.right_inv e)

/-- The complete transported graft is recursively isomorphic with its
actual induced boundary action. No original input order is silently erased. -/
noncomputable def iso : BoundaryIso (net P G j) (net P H (image f j)) :=
  (occurrence P f j).boundaryIso_of_edge_surjective (inputs P f j)
    (by intro i; rw [output_port];trivial) (cover P f j)

/-- Every upstream input keeps its numerical position in the transported graft. -/
theorem iso_upstream (i : Fin (List.replicate a s.wire).length) :
    (iso P f j).inputs.toFun ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at *;omega⟩ =
      ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at *;omega⟩ := by
  apply Port.input.inj (Internal := (net P H (image f j)).Internal) (outputs := O.length)
  have mapped := (iso P f j).map_input ⟨i.val,by have:=i.isLt;simp only [List.length_replicate] at *;omega⟩
  change (occurrence P f j).ports (.input _) = .input ((iso P f j).inputs.toFun _) at mapped
  exact mapped.symm.trans (upstream_port P f j i)

/-- Delete the selected position on each side, then apply the recorded
input bijection. This is the complete induced action on remaining inputs. -/
theorem iso_downstream (i : Fin (b+1)) (ne : i ≠ j) :
    (iso P f j).inputs.toFun (remaining (s := s) (a := a) j i ne) =
      remaining (s := s) (a := a) (image f j) (image f i)
        (fun eq => ne (image_injective f eq)) := by
  apply Port.input.inj (Internal := (net P H (image f j)).Internal) (outputs := O.length)
  have mapped := (iso P f j).map_input (remaining (s := s) (a := a) j i ne)
  change (occurrence P f j).ports (.input _) = .input ((iso P f j).inputs.toFun _) at mapped
  exact mapped.symm.trans (downstream_port P f j i ne)

/-- Every external output follows exactly the original downstream action. -/
theorem iso_output (i : Fin O.length) : (iso P f j).outputs.toFun i = f.outputs.toFun i := by
  apply Port.output.inj (Internal := (net P H (image f j)).Internal)
    (inputs := (List.replicate (a+b) s.wire).length)
  have mapped := (iso P f j).map_output i
  change (occurrence P f j).ports (.output i) = .output ((iso P f j).outputs.toFun i) at mapped
  exact mapped.symm.trans (output_port P f j i)

/-- A nonempty upstream active input zero is fixed exactly. -/
theorem active (positive : 0<a) :
    (iso P f j).inputs.toFun ⟨0,by simp;omega⟩ = ⟨0,by simp;omega⟩ :=
  iso_upstream P f j ⟨0,by simpa using positive⟩

omit P j in
theorem image_congr {K : List Wire}
    {G' H' : Hypernet d (List.replicate (b+1) s.wire) K}
    (g : BoundaryIso G' H') (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i)
    (i : Fin (b+1)) : image f i = image g i := by
  apply Fin.ext
  exact congrArg (fun x : Fin (List.replicate (b+1) s.wire).length => x.val)
    (same ⟨i.val,by simp⟩)

/-- Equal downstream input actions induce equal whole-graft input actions,
even if the downstream graphs have different output interfaces. -/
theorem same_inputs {K : List Wire}
    {G' H' : Hypernet d (List.replicate (b+1) s.wire) K}
    (g : BoundaryIso G' H') (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i) :
    ∀ i, (iso P f j).inputs.toFun i = (iso P g j).inputs.toFun i := by
  intro i
  rcases input_covered s a b O j i with ⟨x,eq⟩ | ⟨x,eq⟩
  · have index : (⟨x.val,by simp;omega⟩ : Fin (List.replicate (a+b) s.wire).length) = i := Port.input.inj eq
    rw [← index,iso_upstream P f j ⟨x.val,by simp⟩,iso_upstream P g j ⟨x.val,by simp⟩]
  · have ne : x ≠ j := by
      intro same
      subst x
      rw [downstream_selected] at eq
      cases eq
    have index : remaining (s := s) (a := a) j x ne = i := by
      apply Port.input.inj (Internal := Fin 1) (outputs := O.length)
      simpa only [downstream,ne,↓reduceDIte,remaining] using eq
    rw [← index,iso_downstream,iso_downstream]
    simp only [remaining,image_congr f g same]

end Hypernets.Copying.ContractionTree.Graft.BoundaryRight

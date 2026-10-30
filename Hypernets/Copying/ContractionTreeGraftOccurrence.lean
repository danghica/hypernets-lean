import Hypernets.Copying.ContractionTreeGraft
import Hypernets.Copying.ExpansionOccurrenceJoin

/-! Complete occurrences glue at one ordered downstream input. The actual
graft retains all other input positions; disjoint edge support supplies the
required internal-carrier freshness through complete incidence matching. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft.Join
open Graph Opening
variable {d a b : Nat} {s : ShareSort} {O I K : List Wire}
    {P : Hypernet d (List.replicate a s.wire) [s.wire]}
    {G : Hypernet d (List.replicate (b+1) s.wire) O} {H : Hypernet d I K}
    (f : Occurrence P H) (g : Occurrence G H) (j : Fin (b+1))

/-- Select the unique original component owning an external graft input.
Coverage, rather than an ordering quotient, supplies this finite inverse. -/
noncomputable def inputPort (i : Fin (List.replicate (a+b) s.wire).length) : H.Vertex := by
  classical
  exact if first : ∃ x, upstream s a b O x = .input i then
    f.ports (.input ⟨(Classical.choose first).val,by simp⟩)
  else g.ports (.input ⟨(Classical.choose ((input_covered s a b O j i).resolve_left first)).val,by simp⟩)

noncomputable def host : (pattern s a b O j d).Vertex → H.Vertex
  | .internal _ => f.ports (.output 0)
  | .input i => inputPort f g j i
  | .output i => g.ports (.output i)

theorem upstream_port (i : Fin a) :
    host f g j (upstream s a b O i) = f.ports (.input ⟨i.val,by simp⟩) := by
  classical
  have first : ∃ x, upstream s a b O x = (.input ⟨i.val,by simp; omega⟩ : Vertex s a b O) := ⟨i,rfl⟩
  change inputPort f g j ⟨i.val,by simp; omega⟩ = _
  simp only [inputPort,dite_eq_left first]
  have same := upstream_injective s a b O (Classical.choose_spec first)
  have values := congrArg (fun x : Fin a => x.val) same
  exact congrArg f.ports (congrArg Port.input (Fin.ext values))

theorem downstream_input (i : Fin (b+1)) (k : Fin (List.replicate (a+b) s.wire).length)
    (eq : downstream s a b O j i = .input k) :
    host f g j (.input k) = g.ports (.input ⟨i.val,by simp⟩) := by
  classical
  have no : ¬ ∃ x, upstream s a b O x = .input k := by
    rintro ⟨x,h⟩
    exact upstream_downstream_ne s a b O j x i (h.trans eq.symm)
  change inputPort f g j k = _
  simp only [inputPort,dite_eq_right no]
  have same := downstream_injective s a b O j
    ((Classical.choose_spec ((input_covered s a b O j k).resolve_left no)).trans eq.symm)
  have values := congrArg (fun x : Fin (b+1) => x.val) same
  exact congrArg g.ports (congrArg Port.input (Fin.ext values))

theorem downstream_port (link : f.ports (.output 0) = g.ports (.input ⟨j.val,by simp⟩))
    (i : Fin (b+1)) :
    host f g j (downstream s a b O j i) = g.ports (.input ⟨i.val,by simp⟩) := by
  by_cases same : i=j
  · subst i
    rw [downstream_selected]
    exact link
  · have existsInput : ∃ k, downstream s a b O j i = .input k := by
      unfold downstream
      rw [dite_eq_right same]
      exact ⟨_,rfl⟩
    obtain ⟨k,eq⟩ := existsInput
    rw [eq]
    exact downstream_input f g j i k eq

noncomputable def each (e : (pattern s a b O j d).Edge) :
    Occurrence (filling P G j e) H := by
  cases d <;> cases e
  all_goals first | exact f | exact g

theorem source (link : f.ports (.output 0) = g.ports (.input ⟨j.val,by simp⟩))
    (e : (pattern s a b O j d).Edge) (i) :
    (each f g j e).ports (.input i) = host f g j ((pattern s a b O j d).sourcePort e i) := by
  cases d <;> cases e
  all_goals simp only [pattern,Net.relabel,frame,Net.sourcePort,sources,List.getElem_map,List.getElem_finRange]
  all_goals
    first
    | (change Fin (List.replicate a s.wire).length at i
       exact (upstream_port f g j ⟨i.val,by simpa only [List.length_replicate] using i.isLt⟩).symm)
    | (change Fin (List.replicate (b+1) s.wire).length at i
       exact (downstream_port f g j link ⟨i.val,by simpa only [List.length_replicate] using i.isLt⟩).symm)

theorem target (e : (pattern s a b O j d).Edge) (i) :
    (each f g j e).ports (.output i) = host f g j ((pattern s a b O j d).targetPort e i) := by
  cases d <;> cases e
  all_goals first
    | (change Fin 1 at i; have zero : i=0 := Subsingleton.elim _ _; subst i; rfl)
    | (simp only [pattern,Net.relabel,frame,Net.targetPort,targets,List.getElem_map,List.getElem_finRange]; rfl)

theorem components_disjoint (disjoint : ∀ e c, f.edges e ≠ g.edges c)
    (x y : (pattern s a b O j d).Edge) (ne : x≠y) :
    ∀ e c, (each f g j x).edges e ≠ (each f g j y).edges c := by
  cases d <;> cases x <;> cases y
  all_goals first
    | exact False.elim (ne rfl)
    | exact disjoint
    | exact fun e c eq => disjoint c e eq.symm

variable (link : f.ports (.output 0) = g.ports (.input ⟨j.val,by simp⟩))
    (disjoint : ∀ e c, f.edges e ≠ g.edges c)

/-- Assemble the original graft occurrence from its actual two complete
components and their one specified shared boundary attachment. -/
noncomputable def occurrence : Occurrence (net P G j) H :=
  Occurrence.ExpansionJoin.occurrence _ _ (each f g j) (host f g j)
    (source f g j link) (target f g j) (components_disjoint f g j disjoint)

theorem left_port (v : P.Vertex) :
    (occurrence f g j link disjoint).ports (leftInsert P G j v) = f.ports v := by
  cases d <;> exact Occurrence.ExpansionJoin.occurrence_insert (pattern s a b O j _) (filling P G j)
    (each f g j) (host f g j) (source f g j link) (target f g j) (components_disjoint f g j disjoint) false v

theorem right_port (v : G.Vertex) :
    (occurrence f g j link disjoint).ports (rightInsert P G j v) = g.ports v := by
  cases d <;> exact Occurrence.ExpansionJoin.occurrence_insert (pattern s a b O j _) (filling P G j)
    (each f g j) (host f g j) (source f g j link) (target f g j) (components_disjoint f g j disjoint) true v

theorem left_edge (e : P.Edge) :
    (occurrence f g j link disjoint).edges ((leftOccurrence P G j).edges e) = f.edges e := by
  cases d <;> rfl

theorem right_edge (e : G.Edge) :
    (occurrence f g j link disjoint).edges ((rightOccurrence P G j).edges e) = g.edges e := by
  cases d <;> rfl

end Hypernets.Copying.ContractionTree.Graft.Join

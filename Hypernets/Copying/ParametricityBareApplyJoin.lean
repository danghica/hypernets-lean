import Hypernets.Copying.ParametricityBareApply

/-! An actual application head and a complete family occurrence assemble the
bare application footprint. The argument remains an original host wire. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BareApplyFirst.Join
open Graph Opening
variable {d n I O} (G : Hypernet d (List.replicate (n+1) .term) [])
    {H : Hypernet d I O} (a : Occurrence (primitiveNet d (.operation .app)) H)
    (f : Occurrence G H)

def host : (pattern n d).Vertex → H.Vertex
  | .internal _ => a.ports (.output (0 : Fin 2))
  | .input i => if i.val=0 then a.ports (.input (0 : Fin 1)) else f.ports (.input i)
  | .output _ => a.ports (.output (1 : Fin 2))

noncomputable def components (e : Bool) : Occurrence (filling G e) H := by
  cases d <;> cases e
  all_goals first | exact a | exact f

variable (link : a.ports (.output (0 : Fin 2)) = f.ports (.input ⟨0,by simp⟩))
    (disjoint : ∀ e x, a.edges e ≠ f.edges x)

include link in
theorem inputs : ∀ e i, (components G a f e).ports (.input i) =
    host G a f ((pattern n d).sourcePort e i) := by
  intro e i
  cases e
  · cases d
    all_goals
      change Fin 1 at i
      have zero : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  · cases d
    all_goals
      change Fin (List.replicate (n+1) Wire.term).length at i
      have bound : i.val<n+1 := by simpa using i.isLt
      by_cases zero : i.val=0
      · have eq : i=⟨0,by simp⟩ := Fin.ext zero
        subst i
        exact link.symm
      · let j : Fin n := ⟨i.val-1,by omega⟩
        have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
        rw [eq]
        change f.ports (.input ⟨j.val+1,_⟩) = host G a f ((pattern n _).sourcePort true ⟨j.val+1,_⟩)
        simp only [Net.sourcePort,pattern,Net.relabel,frame,sources,List.getElem_cons_succ,
          List.getElem_map,List.getElem_finRange,remaining,host]
        rw [ite_eq_right (by omega)]
        rfl

theorem outputs : ∀ e i, (components G a f e).ports (.output i) =
    host G a f ((pattern n d).targetPort e i) := by
  intro e i
  cases e
  · cases d
    all_goals
      change Fin 2 at i
      have choices : i=(0 : Fin 2) ∨ i=1 := by
        by_cases z : i.val=0
        · exact .inl (Fin.ext z)
        · exact .inr (Fin.ext (by have := i.isLt; omega))
      rcases choices with rfl | rfl <;> rfl
  · cases d <;> exact Fin.elim0 i

/-- All actual internal and boundary incidences are supplied by the original
complete occurrences; disjointness is the only freshness requirement. -/
noncomputable def occurrence : Occurrence (net G) H :=
  Occurrence.ExpansionJoin.occurrence (pattern n d) (filling G) (components G a f)
    (host G a f) (inputs G a f link) (outputs G a f) (by
      cases d
      all_goals
        intro e b ne x y eq
        cases e <;> cases b
        · exact ne rfl
        · exact disjoint x y eq
        · exact disjoint y x eq.symm
        · exact ne rfl)

theorem input_zero : (occurrence G a f link disjoint).ports (.input ⟨0,by simp⟩) =
    a.ports (.input (0 : Fin 1)) := rfl

theorem input_succ (i : Fin n) :
    (occurrence G a f link disjoint).ports (.input ⟨i.val+1,by simp⟩) =
      f.ports (.input ⟨i.val+1,by simp⟩) := by
  change (if i.val+1=0 then a.ports (.input (0 : Fin 1)) else f.ports (.input ⟨i.val+1,by simp⟩)) = _
  rw [ite_eq_right (by omega)]

theorem output : (occurrence G a f link disjoint).ports (.output 0) =
    a.ports (.output (1 : Fin 2)) := rfl

end Hypernets.Copying.Parametricity.BareApplyFirst.Join

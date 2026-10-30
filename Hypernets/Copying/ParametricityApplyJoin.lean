import Hypernets.Copying.ParametricityApplyFirst
import Hypernets.Copying.ExpansionOccurrenceJoin

/-! Complete actual app/family/argument occurrences assemble the original
first-input application context, including all remaining external inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ApplyFirst.Join
open Graph Opening
variable {d n O I K} (G : Hypernet d (List.replicate (n+1) .term) [])
    (V : Hypernet d [.term] O) {H : Hypernet d I K}
    (a : Occurrence (primitiveNet d (.operation .app)) H)
    (f : Occurrence G H) (v : Occurrence V H)

/-- Original frame attachments, with the selected application at input0. -/
def host : (pattern n O d).Vertex → H.Vertex
  | .internal i => a.ports (.output i)
  | .input i => if i.val=0 then a.ports (.input (0 : Fin 1)) else f.ports (.input i)
  | .output i => v.ports (.output i)

noncomputable def components (e : Option Bool) : Occurrence (filling G V e) H := by
  cases d <;> cases e with
  | none => exact a
  | some b => cases b
              · exact f
              · exact v

variable (functionLink : a.ports (.output (0 : Fin 2)) = f.ports (.input ⟨0,by simp⟩))
    (argumentLink : a.ports (.output (1 : Fin 2)) = v.ports (.input (0 : Fin 1)))

include functionLink argumentLink in
theorem inputs : ∀ e i, (components G V a f v e).ports (.input i) =
    host G V a f v ((pattern n O d).sourcePort e i) := by
  intro e i
  cases e with
  | none =>
    cases d
    all_goals
      change Fin 1 at i
      have zero : i=(0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rfl
  | some b =>
    cases b
    · cases d
      all_goals
        change Fin (List.replicate (n+1) Wire.term).length at i
        have bound : i.val<n+1 := by simpa using i.isLt
        by_cases zero : i.val=0
        · have eq : i = ⟨0,by simp⟩ := Fin.ext zero
          subst i
          exact functionLink.symm
        · let j : Fin n := ⟨i.val-1,by omega⟩
          have eq : i=⟨j.val+1,by simp⟩ := Fin.ext (by dsimp [j]; omega)
          rw [eq]
          change f.ports (.input ⟨j.val+1,_⟩) = host G V a f v ((pattern n O _).sourcePort (some false) ⟨j.val+1,_⟩)
          simp only [Net.sourcePort,pattern,Net.relabel,frame,sources,List.getElem_cons_succ,
            List.getElem_map,List.getElem_finRange,remaining,host]
          rw [ite_eq_right (by omega)]
          rfl
    · cases d
      all_goals
        change Fin 1 at i
        have zero : i=(0 : Fin 1) := Subsingleton.elim _ _
        subst i
        exact argumentLink.symm

omit functionLink argumentLink in
theorem outputs : ∀ e i, (components G V a f v e).ports (.output i) =
    host G V a f v ((pattern n O d).targetPort e i) := by
  intro e i
  cases e with
  | none =>
    cases d
    all_goals
      change Fin 2 at i
      have cases : i=(0 : Fin 2) ∨ i=1 := by
        by_cases z : i.val=0
        · exact .inl (Fin.ext z)
        · exact .inr (Fin.ext (by have := i.isLt; omega))
      rcases cases with rfl | rfl <;> rfl
  | some b =>
    cases b
    · cases d <;> exact Fin.elim0 i
    · cases d
      all_goals
        change v.ports (.output i) = host G V a f v ((pattern n O _).targetPort (some true) i)
        simp only [Net.targetPort,pattern,Net.relabel,frame,targets,List.getElem_map,List.getElem_finRange,host]
        rfl

variable (af : ∀ e x, a.edges e ≠ f.edges x) (av : ∀ e x, a.edges e ≠ v.edges x)
    (fv : ∀ e x, f.edges e ≠ v.edges x)

omit functionLink argumentLink in
include af av fv in
theorem disjoint : ∀ e b, e ≠ b → ∀ x y,
    (components G V a f v e).edges x ≠ (components G V a f v b).edges y := by
  cases d
  all_goals
    intro e b ne x y eq
    cases e with
    | none =>
      cases b with
      | none => exact ne rfl
      | some b => cases b
                  · exact af x y eq
                  · exact av x y eq
    | some e =>
      cases b with
      | none => cases e
                · exact af y x eq.symm
                · exact av y x eq.symm
      | some b => cases e <;> cases b
                  · exact ne rfl
                  · exact fv x y eq
                  · exact fv y x eq.symm
                  · exact ne rfl

/-- Every original ordered incidence is realized by the supplied complete
occurrences. Their proven disjointness supplies all necessary freshness. -/
noncomputable def occurrence : Occurrence (net G V) H :=
  Occurrence.ExpansionJoin.occurrence (pattern n O d) (filling G V) (components G V a f v)
    (host G V a f v) (inputs G V a f v functionLink argumentLink) (outputs G V a f v)
    (disjoint G V a f v af av fv)

theorem input_zero : (occurrence G V a f v functionLink argumentLink af av fv).ports (.input ⟨0,by simp⟩) =
    a.ports (.input (0 : Fin 1)) := rfl

theorem input_succ (i : Fin n) :
    (occurrence G V a f v functionLink argumentLink af av fv).ports (.input ⟨i.val+1,by simp⟩) =
      f.ports (.input ⟨i.val+1,by simp⟩) := by
  change (if i.val+1=0 then a.ports (.input (0 : Fin 1)) else f.ports (.input ⟨i.val+1,by simp⟩)) = _
  rw [ite_eq_right (by omega)]

theorem output (i : Fin O.length) :
    (occurrence G V a f v functionLink argumentLink af av fv).ports (.output i) = v.ports (.output i) := rfl

end Hypernets.Copying.Parametricity.ApplyFirst.Join

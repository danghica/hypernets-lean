import Hypernets.Copying.CopyingNestedRows

/-! Both literal associations of complete binary distributor rows occur in
an actual host. The middle link is the only attachment premise; complete
incidence proves all necessary internal freshness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingNested.Row
open Graph Opening
variable {d I O s} {G : Hypernet d I O}
    (inner outer : Occurrence (CanonicalTree.atDepth s 2 d) G) (associateRight : Bool)

def occurrenceHost : (frame s associateRight d).net.Vertex → G.Vertex
  | .input i => if associateRight then
      if i.val = 0 then outer.ports (.input ⟨0,by simp⟩)
      else if i.val = 1 then inner.ports (.input ⟨0,by simp⟩)
      else inner.ports (.input ⟨1,by simp⟩)
    else if i.val = 0 then inner.ports (.input ⟨0,by simp⟩)
      else if i.val = 1 then inner.ports (.input ⟨1,by simp⟩)
      else outer.ports (.input ⟨1,by simp⟩)
  | .output _ => outer.ports (.output 0)
  | .internal _ => inner.ports (.output 0)

def occurrenceComponents (b : (frame s associateRight d).net.Edge) :
    Occurrence (family s associateRight d b) G := by
  cases d <;> exact if (show Bool from b) then outer else inner

variable (link : inner.ports (.output 0) =
    outer.ports (.input (if associateRight then ⟨1,by simp⟩ else ⟨0,by simp⟩)))
    (disjoint : ∀ e a, inner.edges e ≠ outer.edges a)
include link disjoint

/-- The complete two-row graph, including both canonical weakenings,
is an actual complete-label occurrence in its original host. -/
noncomputable def occurrence : Occurrence (graph s associateRight d) G := by
  apply Occurrence.ExpansionJoin.occurrence (frame s associateRight d).net
    (family s associateRight d) (occurrenceComponents inner outer associateRight)
    (occurrenceHost inner outer associateRight)
  · intro e i
    cases d <;> cases e
    all_goals
      change Fin 2 at i
      have alternatives : i = (0 : Fin 2) ∨ i = (1 : Fin 2) := by
        by_cases zero : i.val = 0
        · exact .inl (Fin.ext zero)
        · exact .inr (Fin.ext (by have := i.isLt; omega))
      rcases alternatives with rfl | rfl
    all_goals cases associateRight
    all_goals first | rfl | exact link.symm
  · intro e i
    cases d <;> cases e
    all_goals
      change Fin 1 at i
      have zero : i = 0 := Subsingleton.elim _ _
      subst i
      rfl
  · intro e a different b c
    cases d <;> cases e <;> cases a
    all_goals first
      | exact False.elim (different rfl)
      | exact disjoint b c
      | exact fun eq => disjoint c b eq.symm

theorem occurrence_input (i : Fin 3) :
    (occurrence inner outer associateRight link disjoint).ports (.input ⟨i.val,by simp⟩) =
      occurrenceHost inner outer associateRight (.input ⟨i.val,by simp⟩) := rfl

theorem occurrence_output :
    (occurrence inner outer associateRight link disjoint).ports (.output 0) =
      outer.ports (.output 0) := rfl

end Hypernets.Copying.CopyingNested.Row

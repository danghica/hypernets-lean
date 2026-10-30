import Hypernets.Graph.SetPresentation
import Hypernets.Graph.FiniteTrace

/-! Finite components selected by forward convergence to a distinguished edge.
The distinguished output may be internal in the original host. -/
namespace Hypernets.Graph
universe u
namespace Net
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- A selected component has one exit, functional forward incidence, and an
actual finite path from each selected edge to the distinguished root. -/
structure RootedBasin (G : Net σ I O) (sort : L) where
  chosen : G.Edge → Prop
  root : G.Edge
  output : G.Vertex
  root_chosen : chosen root
  root_target : G.target root = [output]
  single : ∀ e, chosen e → (G.target e).length = 1
  reaches : ∀ e, chosen e → ∃ n, Trace (fun a b => chosen a ∧ G.Adjacent a b ∧ chosen b) e root n
  terminal : ∀ f, chosen f → ¬ G.Adjacent root f
  source_label : ∀ e, chosen e → ∀ v, v ∈ G.source e → G.vertexLabel v = sort
  target_label : ∀ e, chosen e → ∀ v, v ∈ G.target e → G.vertexLabel v = sort

namespace RootedBasin
variable {G : Net σ I O} {sort : L} (S : RootedBasin G sort)

def Next (e f : G.Edge) : Prop := S.chosen e ∧ G.Adjacent e f ∧ S.chosen f

theorem functional {a b c} (ab : S.Next a b) (ac : S.Next a c) : b = c :=
  G.adjacent_functional_at (S.single a ab.1) ab.2.1 ac.2.1

theorem root_terminal : Terminal S.Next S.root := fun f h => S.terminal f h.2.2 h.2.1

noncomputable def distance (e : {e : G.Edge // S.chosen e}) : Nat :=
  Classical.choose (S.reaches e.val e.property)

theorem distance_trace (e : {e : G.Edge // S.chosen e}) : Trace S.Next e.val S.root (S.distance e) :=
  Classical.choose_spec (S.reaches e.val e.property)

theorem distance_step {e f : {e : G.Edge // S.chosen e}} (adj : G.Adjacent e.val f.val) :
    S.distance e = S.distance f + 1 := by
  have step : S.Next e.val f.val := ⟨e.property,adj,f.property⟩
  exact (Trace.terminal_unique (R := S.Next) (fun h h' => S.functional h h') (S.distance_trace e)
    (.step step (S.distance_trace f)) S.root_terminal S.root_terminal).2

/-- Forward convergence forbids a selected consumer at the distinguished exit. -/
theorem output_not_source (e : {e : G.Edge // S.chosen e}) : S.output ∉ G.source e.val := by
  intro h
  exact S.terminal e.val e.property ⟨S.output,by rw [S.root_target]; simp,h⟩

/-- A selected non-root producer is followed by another selected edge. -/
theorem next_of_ne {e : G.Edge} (chosen : S.chosen e) (ne : e ≠ S.root) :
    ∃ f, S.chosen f ∧ G.Adjacent e f := by
  obtain ⟨n,path⟩ := S.reaches e chosen
  cases path with
  | refl => exact False.elim (ne rfl)
  | step edge _ => exact ⟨_,edge.2.2,edge.2.1⟩

end RootedBasin
end Net
end Hypernets.Graph

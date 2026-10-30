import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.EqualPrefixCosts

/-! Exact finite execution inside a constructed complete-match complement.
The local run is lifted before any observation or termination is compared. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

theorem castInterfaces_eq_reboundary {d I O J K} (hi : I = J) (ho : O = K)
    (s : State d I O) : castInterfaces hi ho s =
      ⟨s.1.reboundary hi ho,(s.2.1,Port.cast hi ho s.2.2)⟩ := by
  cases hi; cases ho
  rcases s with ⟨G,m,v⟩
  apply Sigma.ext (Net.reboundary_refl G).symm
  simp only [castInterfaces,Port.cast_refl]
  rfl
end Hypernets.Copying.Combined

namespace Hypernets.Copying.CompleteMatchCut
open Graph Combined
variable {d I O J K} {A : Hypernet d J K} {G : Hypernet d I O}
    (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e)))

noncomputable def replaceState (s : State d J K) : State d I O :=
  ⟨replaceWith f labels s.1,(s.2.1,replacePort f labels s.1 s.2.2)⟩

theorem run_replace {s t : State d J K} {n}
    (run : (machine d J K).Steps n s t) :
    (machine d I O).Steps n (replaceState f labels s) (replaceState f labels t) := by
  have lifted := run_plug (net f labels) none
    (run_castInterfaces (hole_input f labels).symm (hole_output f labels).symm run)
  rw [castInterfaces_eq_reboundary,castInterfaces_eq_reboundary] at lifted
  exact lifted

/-- The constructed replacement of the original matched source recovers the
actual source token and graph, including boundary ports. -/
noncomputable def sourceIso (mode : Focus) (v : A.Vertex) :
    StateIso (replaceState f labels ⟨A,(mode,v)⟩) ⟨G,(mode,f.ports v)⟩ where
  graph := realization f labels
  mode := rfl
  vertex := map_insert f labels v

/-- An arbitrary finite local run lifts to the original host with exactly its
length; its endpoint is recursively isomorphic to the computed cut replacement. -/
theorem run {mode : Focus} {v : A.Vertex} {t : State d J K} {n}
    (steps : (machine d J K).Steps n ⟨A,(mode,v)⟩ t) :
    ∃ target, (machine d I O).Steps n ⟨G,(mode,f.ports v)⟩ target ∧
      Nonempty (StateIso (replaceState f labels t) target) :=
  run_transport (run_replace f labels steps) (sourceIso f labels mode v)

/-- A local rule whose target is the matched component can be plugged into
that component's actual complement. This constructs a genuine predecessor. -/
theorem rewrite_into {B : Hypernet d J K} {v : B.Vertex} {w : A.Vertex}
    (step : Rewrite B v A w) :
    Rewrite (replaceWith f labels B) (replacePort f labels B v) G (f.ports w) := by
  have lifted := Rewrite.plug (net f labels) none
    (rewrite_reboundary (hole_input f labels).symm (hole_output f labels).symm step)
  have actual := lifted.rename (DeepIso.refl _) (realization f labels)
  have token := map_insert f labels w
  change Port.map (realization f labels).vertices.toFun _ = f.ports w at token
  rw [← token]
  simpa only [replacement,replaceWith,replacePort,DeepIso.refl,Net.RelIso.refl,
    Bijection.refl,Port.map_id_fun,id_eq] using actual

/-- If the local prefix begins with a genuine rewrite, its entire finite run
starts in the original host and ends at the literal complement replacement. -/
theorem run_after_rewrite {B : Hypernet d J K} {v : A.Vertex} {w : B.Vertex}
    (first : Rewrite A v B w) {t : State d J K} {n}
    (rest : (machine d J K).Steps n ⟨B,(.search,w)⟩ t) :
    (machine d I O).Steps (n+1) ⟨G,(.rewrite,f.ports v)⟩ (replaceState f labels t) :=
  .cons (.rewrite (rewrite f labels first)) (run_replace f labels rest)

end Hypernets.Copying.CompleteMatchCut

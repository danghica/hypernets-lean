import Hypernets.Copying.PrimitiveRuleFootprints

/-! Exhaustive source-overlap classification for actual contextual rewrites in
arbitrary original BPerm specimens. Matching is distinguished from rewriting. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined MatchEmbedding

/-- A genuine local rule footprint and its constructed match on the other side.
This certificate does not yet claim a matching right-hand whole-graph rewrite. -/
def PrimitiveMatchPair {d I O} (G H : Hypernet d I O) (v : G.Vertex) (w : H.Vertex) : Prop :=
  ∃ J K, ∃ A B : Hypernet d J K, ∃ a b, Local A a B b ∧ PrimitiveFootprint A ∧
    ∃ left : MatchEmbedding A G, ∃ right : MatchEmbedding A H,
      left.ports a = v ∧ right.ports a = w

/-- Every arbitrary actual rewrite lies in one of these three source cases.
The basic-operation case has both matches constructed with exact port order. -/
theorem rewrite_cases {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    {H : Hypernet d I O} {v w} (step : Rewrite (C.expand L) v H w) :
    PrimitiveMatchPair (C.expand L) (C.expand R) v
      (Net.Expansion.host C R (PrimitiveMatching.down C cert v)) ∨
    (∃ e, HeadAt (C.expand L) v e (.operation .app)) ∨
    ∃ e, HeadAt (C.expand L) v e (.contraction .term) := by
  obtain ⟨J,K,A,B,a,b,localStep,f,atToken⟩ := step.local_source
  rcases localStep.footprint_cases with basic | beta | copy
  · refine .inl ⟨J,K,A,B,a,b,localStep,basic,f,PrimitiveMatching.across C cert f basic,atToken,?_⟩
    change Net.Expansion.host C R (PrimitiveMatching.down C cert (f.ports a)) = _
    rw [atToken]
  · obtain ⟨e,head⟩ := beta
    exact .inr (.inl ⟨f.edges e,atToken ▸ f.head head⟩)
  · obtain ⟨e,head⟩ := copy
    exact .inr (.inr ⟨f.edges e,atToken ▸ f.head head⟩)

/-- A recognized basic-operation head selects the constructed primitive match
case, without requiring the caller to classify its contextual rewrite derivation. -/
theorem rewrite_basic_case {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    {H : Hypernet d I O} {v w e p} (step : Rewrite (C.expand L) v H w)
    (head : HeadAt (C.expand L) v e p)
    (notApp : p ≠ .operation .app) (notCopy : p ≠ .contraction .term) :
    PrimitiveMatchPair (C.expand L) (C.expand R) v
      (Net.Expansion.host C R (PrimitiveMatching.down C cert v)) := by
  rcases rewrite_cases C cert step with basic | beta | copy
  · exact basic
  · obtain ⟨e,h⟩ := beta
    exact False.elim (notApp (head_unique head h).2)
  · obtain ⟨e,h⟩ := copy
    exact False.elim (notCopy (head_unique head h).2)

/-- The original specimen interface supplies every classification premise. -/
theorem specimen_rewrite_cases {Allowed} (S : Specimen template Allowed)
    {H : Hypernet S.depth [.term] []} {w}
    (step : Rewrite (S.context.expand S.left) (Net.Expansion.host S.context S.left S.token.2) H w) :
    PrimitiveMatchPair (S.context.expand S.left) (S.context.expand S.right)
      (Net.Expansion.host S.context S.left S.token.2) (Net.Expansion.host S.context S.right S.token.2) ∨
    (∃ e, HeadAt (S.context.expand S.left) (Net.Expansion.host S.context S.left S.token.2) e (.operation .app)) ∨
    ∃ e, HeadAt (S.context.expand S.left) (Net.Expansion.host S.context S.left S.token.2) e (.contraction .term) := by
  simpa only [PrimitiveMatching.down_host] using rewrite_cases S.context S.edges step
end Hypernets.Copying.BoxPermutation

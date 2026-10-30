import Hypernets.Copying.SharingBasin

/-! Maximal sharing basins ending at distinct stores cannot share an edge.
This follows from unique ordered output incidence and actual finite traces. -/
namespace Hypernets.Copying.SharingBasin
open Graph

/-- An actual sharing predecessor has only one terminal sharing root. -/
theorem predecessor_roots_equal {d I O} (G : Hypernet d I O) (s : ShareSort)
    {e a b : G.Edge}
    (left : G.PredecessorOf (Eligible G s) a e)
    (right : G.PredecessorOf (Eligible G s) b e)
    (leftTerminal : ∀ x, Eligible G s x → ¬ G.Adjacent a x)
    (rightTerminal : ∀ x, Eligible G s x → ¬ G.Adjacent b x) : a = b := by
  obtain ⟨_,m,lp⟩ := left
  obtain ⟨_,n,rp⟩ := right
  have functional : ∀ {u v w}, G.SharingNext (Eligible G s) u v →
      G.SharingNext (Eligible G s) u w → v = w := by
    intro u v w uv uw
    exact G.adjacent_functional_at (single G s u uv.1) uv.2.1 uw.2.1
  have lt : Terminal (G.SharingNext (Eligible G s)) a :=
    fun x next => leftTerminal x next.2.2 next.2.1
  have rt : Terminal (G.SharingNext (Eligible G s)) b :=
    fun x next => rightTerminal x next.2.2 next.2.1
  exact (Trace.terminal_unique (R := G.SharingNext (Eligible G s))
    (fun h h' => functional h h') lp rp lt rt).1

/-- Distinct terminal stores force disjoint complete predecessor basins. -/
theorem predecessor_disjoint {d I O} (G : Hypernet d I O) (s : ShareSort)
    {a b : G.Edge} (different : a ≠ b)
    (leftTerminal : ∀ x, Eligible G s x → ¬ G.Adjacent a x)
    (rightTerminal : ∀ x, Eligible G s x → ¬ G.Adjacent b x) :
    ∀ e, ¬ (G.PredecessorOf (Eligible G s) a e ∧ G.PredecessorOf (Eligible G s) b e) := by
  rintro e ⟨left,right⟩
  exact different (predecessor_roots_equal G s left right leftTerminal rightTerminal)

/-- A nonsharing consumer makes a selected component's root terminal even
among all sharing-like host edges, not only among its chosen edges. -/
theorem terminal_at_consumer {d I O} (G : Hypernet d I O) (s : ShareSort)
    (S : G.RootedBasin s.wire) {head : G.Edge}
    (source : S.output ∈ G.source head)
    (nonsharing : ¬ SharingLabel d s (G.edgeLabel head)) :
    ∀ e, Eligible G s e → ¬ G.Adjacent S.root e := by
  rintro e sharing ⟨v,target,mem⟩
  have equal : v = S.output := by simpa only [S.root_target,List.mem_singleton] using target
  subst v
  have same := G.source_unique source mem
  exact nonsharing (same ▸ sharing)

/-- Sharing components feeding distinct nonsharing edges are edge-disjoint.
The statement applies to the existential basin records produced by selection,
without requiring clients to recover a particular predecessor presentation. -/
theorem components_disjoint {d I O} (G : Hypernet d I O) (s : ShareSort)
    (S U : G.RootedBasin s.wire)
    (leftLabels : ∀ e, S.chosen e → Eligible G s e)
    (rightLabels : ∀ e, U.chosen e → Eligible G s e)
    {head other : G.Edge} (leftSource : S.output ∈ G.source head)
    (rightSource : U.output ∈ G.source other)
    (leftNonsharing : ¬ SharingLabel d s (G.edgeLabel head))
    (rightNonsharing : ¬ SharingLabel d s (G.edgeLabel other))
    (different : head ≠ other) : ∀ e, ¬ (S.chosen e ∧ U.chosen e) := by
  rintro e ⟨left,right⟩
  obtain ⟨m,leftTrace⟩ := S.reaches e left
  obtain ⟨n,rightTrace⟩ := U.reaches e right
  have leftPath : Trace (G.SharingNext (Eligible G s)) e S.root m :=
    leftTrace.map id (fun h => ⟨leftLabels _ h.1,h.2.1,leftLabels _ h.2.2⟩)
  have rightPath : Trace (G.SharingNext (Eligible G s)) e U.root n :=
    rightTrace.map id (fun h => ⟨rightLabels _ h.1,h.2.1,rightLabels _ h.2.2⟩)
  have rootEq := predecessor_roots_equal G s
    ⟨leftLabels e left,m,leftPath⟩ ⟨rightLabels e right,n,rightPath⟩
    (terminal_at_consumer G s S leftSource leftNonsharing)
    (terminal_at_consumer G s U rightSource rightNonsharing)
  have outputs : S.output = U.output :=
    (List.cons.inj (S.root_target.symm.trans ((congrArg G.target rootEq).trans U.root_target))).1
  exact different (G.source_unique (outputs ▸ leftSource) rightSource)

end Hypernets.Copying.SharingBasin

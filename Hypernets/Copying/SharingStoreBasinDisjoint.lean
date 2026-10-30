import Hypernets.Copying.SharingBasinDisjoint
import Hypernets.Copying.SharingRootOrigin

/-! Complete sharing components with distinct actual store consumers are
disjoint, independently of how their finite predecessor presentations arose. -/
namespace Hypernets.Copying.SharingBasin
open Graph

/-- An actual store consumer makes a sharing-basin root globally terminal
among sharing labels, not merely terminal inside its chosen subset. -/
theorem store_terminal {d I O} (C : Hypernet d I O) (S : C.RootedBasin Wire.atom)
    {store : C.Edge} (label : C.edgeLabel store = primitiveLabel d .store)
    (source : S.output ∈ C.source store) :
    ∀ e, Eligible C .atom e → ¬ C.Adjacent S.root e := by
  rintro e sharing ⟨v,root,consumed⟩
  rw [S.root_target] at root
  have eq : v = S.output := List.mem_singleton.mp root
  subst v
  have same := C.source_unique source consumed
  subst e
  rcases sharing with weak | contraction | ⟨h,n,hole,_,_⟩
  all_goals have bad := primitiveLabel_injective d (label.symm.trans ‹_›)
  all_goals cases bad

/-- Any two complete sharing components attached to distinct original stores
have disjoint edge sets. Both paths are mapped into one functional relation. -/
theorem stores_disjoint {d I O} (C : Hypernet d I O)
    (S U : C.RootedBasin Wire.atom)
    (leftLabels : ∀ e, S.chosen e → Eligible C .atom e)
    (rightLabels : ∀ e, U.chosen e → Eligible C .atom e)
    {store other : C.Edge} (storeLabel : C.edgeLabel store = primitiveLabel d .store)
    (otherLabel : C.edgeLabel other = primitiveLabel d .store)
    (source : S.output ∈ C.source store) (otherSource : U.output ∈ C.source other)
    (different : store ≠ other) : ∀ e, ¬ (S.chosen e ∧ U.chosen e) := by
  rintro e ⟨left,right⟩
  obtain ⟨n,lp⟩ := S.reaches e left
  obtain ⟨m,rp⟩ := U.reaches e right
  have ltrace : Trace (C.SharingNext (Eligible C .atom)) e S.root n :=
    lp.map id (fun edge => ⟨leftLabels _ edge.1,edge.2.1,leftLabels _ edge.2.2⟩)
  have rtrace : Trace (C.SharingNext (Eligible C .atom)) e U.root m :=
    rp.map id (fun edge => ⟨rightLabels _ edge.1,edge.2.1,rightLabels _ edge.2.2⟩)
  have sameRoot := predecessor_roots_equal C .atom
    ⟨leftLabels _ left,n,ltrace⟩ ⟨rightLabels _ right,m,rtrace⟩
    (store_terminal C S storeLabel source) (store_terminal C U otherLabel otherSource)
  have sameOutput : S.output = U.output := by
    have rows := S.root_target.symm.trans ((congrArg C.target sameRoot).trans U.root_target)
    exact List.singleton_inj.mp rows
  apply different
  exact C.source_unique source (sameOutput ▸ otherSource)

end Hypernets.Copying.SharingBasin

namespace Hypernets.Copying.SharingRootOrigin
open Graph
/-- A retained primitive owner cannot represent two distinct actual edges. -/
theorem retained_owner_injective {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {e g : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (nonsharing : ∀ s, p ≠ .weakening s ∧ p ≠ .contraction s)
    (same : e.1 = g.1) : e = g := by
  obtain ⟨copy⟩ := retained C cert trees label nonsharing
  obtain ⟨a,x⟩ := e
  obtain ⟨b,y⟩ := g
  dsimp at same
  subst b
  exact congrArg (Sigma.mk a) ((copy.only x).trans (copy.only y).symm)
end Hypernets.Copying.SharingRootOrigin

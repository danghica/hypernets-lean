import Hypernets.Copying.ParametricityBoundaryBarrier
import Hypernets.Copying.NullaryRooted

/-! Original search across complete lambda families preserves every common
host coordinate and every transition count. No robustness theorem is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search.Expansion
open Graph
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
    (leftHeads : T.LambdaEntries) (rightHeads : T.converse.LambdaEntries)
    (none : T.NoOutputs) (closed : HoleFree (C.expand L))
include cert leftHeads rightHeads none closed

/-- A search step at an original host coordinate is matched in the other
filled graph. Entering a family returns at the same lambda input; exiting
one is impossible because its actual output interface is empty. -/
theorem lambda_step {p : Position C} {q : Position (C.expand L)}
    (actual : Step (C.expand L) (position C L p) q) :
    ∃ r : Position C, q = position C L r ∧
      Step (C.expand R) (position C R p) (position C R r) := by
  have laws := deepFilling_search cert
  rcases reflect_or_boundary C L laws.2.2.1 p actual with ⟨r,original,eq⟩ | boundary
  · exact ⟨r,eq,step C R laws.2.1 original⟩
  · rcases boundary with ⟨mode,e,h,label,source⟩ | ⟨mode,e,h,label,target⟩
    · have pair := (cert e).relation_at_hole label closed
      obtain ⟨i,eq⟩ := (C.mem_source_iff_port e p.2).mp source
      have token : p = (.search,C.sourcePort e i) := Prod.ext mode eq.symm
      have left := Search.expand_insert C L e ((leftHeads pair).returns i)
      have right := Search.expand_insert C R e ((rightHeads pair).returns i)
      have lp : Step (C.expand L) (position C L p) (position C L (.backtrack,p.2)) := by
        simpa only [token,position,Net.Expansion.insert] using left
      have rp : Step (C.expand R) (position C R p) (position C R (.backtrack,p.2)) := by
        simpa only [token,position,Net.Expansion.insert] using right
      exact ⟨(.backtrack,p.2),Search.deterministic actual lp,rp⟩
    · have pair := (cert e).relation_at_hole label closed
      obtain ⟨i,_⟩ := (C.mem_target_iff_port e p.2).mp target
      exact Fin.elim0 (Fin.cast (congrArg List.length (none pair)) i)

/-- Every finite original search run remains at host coordinates and has
an equally long actual search run through the opposite filled family. -/
theorem lambda_run {p : Position C} {q : Position (C.expand L)} {n}
    (run : (machine (C.expand L)).Steps n (position C L p) q) :
    ∃ r : Position C, q = position C L r ∧
      (machine (C.expand R)).Steps n (position C R p) (position C R r) := by
  generalize start : position C L p = s at run
  induction run generalizing p with
  | zero => exact ⟨p,start.symm,.zero _⟩
  | @cons n s t u first rest ih =>
    subst s
    obtain ⟨r,eq,next⟩ := lambda_step C cert leftHeads rightHeads none closed first
    subst t
    obtain ⟨z,finish,path⟩ := ih rfl
    exact ⟨z,finish,.cons next path⟩

/-- Original search rootedness is equivalent at every common host position,
including internal tokens and independently represented recursive families. -/
theorem lambda_rooted_iff (rightClosed : HoleFree (C.expand R)) (i) (q : Position C) :
    RootedFrom (C.expand L) i (position C L q) ↔
      RootedFrom (C.expand R) i (position C R q) := by
  have forward {A B} (edges : ∀ e, DeepFillingEdge T C A B e)
      (lc : HoleFree (C.expand A))
      (root : RootedFrom (C.expand A) i (position C A q)) :
      RootedFrom (C.expand B) i (position C B q) := by
    obtain ⟨n,run⟩ := root
    obtain ⟨r,finish,path⟩ := lambda_run C edges leftHeads rightHeads none lc (p := (.search,.input i)) run
    have eq : q = r := Prod.ext (congrArg (fun x : Position (C.expand A) => x.1) finish)
      (Net.Expansion.host_injective C A (congrArg Prod.snd finish))
    exact ⟨n,eq ▸ path⟩
  constructor
  · exact forward cert closed
  · intro root
    obtain ⟨n,run⟩ := root
    obtain ⟨r,finish,path⟩ := lambda_run C (fun e => (cert e).converse)
      rightHeads leftHeads none.converse rightClosed (p := (.search,.input i)) run
    have eq : q = r := Prod.ext (congrArg (fun x : Position (C.expand R) => x.1) finish)
      (Net.Expansion.host_injective C R (congrArg Prod.snd finish))
    exact ⟨n,eq ▸ path⟩

end Hypernets.Copying.Search.Expansion

namespace Hypernets.Copying
open Graph

/-- The complete witness transports rootedness by actual search alone;
this lemma does not depend on parametricity robustness or equivalence. -/
theorem FillingWitness.lambda_rooted_iff {T : PreTemplate}
    (leftHeads : T.LambdaEntries) (rightHeads : T.converse.LambdaEntries) (none : T.NoOutputs)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (i : Fin I.length) (q : Search.Position w.context) :
    Search.RootedFrom G i (w.leftPosition q) ↔ Search.RootedFrom H i (w.rightPosition q) := by
  have lc : HoleFree (w.context.expand w.left) := (allLabels_iso_iff _ w.leftIso).mpr left
  have rc : HoleFree (w.context.expand w.right) := (allLabels_iso_iff _ w.rightIso).mpr right
  exact (Search.rooted_iso w.leftIso i (Search.Expansion.position w.context w.left q)).trans
    ((Search.Expansion.lambda_rooted_iff w.context w.edges leftHeads rightHeads none lc rc i q).trans
      (Search.rooted_iso w.rightIso i (Search.Expansion.position w.context w.right q)).symm)

end Hypernets.Copying

import Hypernets.Copying.SharingTreeRequests
import Hypernets.Copying.NullaryPointedExecution

/-! Actual search rootedness survives sharing-template changes at nonrewrite
host positions. Entering a term-sharing hole stops in rewrite mode, so cannot
occur along a search run whose final mode is not rewrite. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (closed : HoleFree (C.expand L))
include cert trees closed

/-- Reflect an entire actual search path, preserving its exact length.
A filled sharing input requests rewriting, and search cannot continue from it. -/
theorem sharing_reflect_nonrewrite_run {i p q n} (rooted : RootedFrom C i p)
    (run : (machine (C.expand L)).Steps n (position C L p) q) (mode : q.1 ≠ .rewrite) :
    ∃ r, (machine C).Steps n p r ∧ q = position C L r := by
  generalize start : position C L p = s at run
  induction run generalizing p with
  | zero => exact ⟨p,.zero _,start.symm⟩
  | @cons n s t u first rest ih =>
    subst s
    have origins := (deepFilling_search cert).2.2.1
    rcases reflect_or_boundary C L origins p first with ⟨r,step,target⟩ | boundary
    · subst t
      obtain ⟨z,path,finish⟩ := ih (rooted_step rooted step) mode rfl
      exact ⟨z,.cons step path,finish⟩
    · rcases boundary with ⟨search,e,h,label,mem⟩ | ⟨backtrack,e,h,label,mem⟩
      · obtain ⟨i,port⟩ := (C.mem_source_iff_port e p.2).mp mem
        have typed : C.vertexLabel p.2 = .term :=
          (Net.Expansion.host_label C L p.2).symm.trans (Search.endpoints_term first).1
        have inputType : ((alphabet d).signature.input (C.edgeLabel e))[i] = .term :=
          (C.sourcePort_label e i).symm.trans (port ▸ typed)
        have pair := (cert e).relation_at_hole label closed
        have request := Search.expand_insert C L e ((trees pair).request i inputType)
        have token : p = (.search,C.sourcePort e i) := Prod.ext search port.symm
        have actual : Search.Step (C.expand L) (position C L p)
            (.rewrite,Net.Expansion.host C L p.2) := by
          simpa only [token,position,Net.Expansion.insert] using request
        have same := Search.deterministic first actual
        subst t
        cases rest with
        | zero => exact False.elim (mode rfl)
        | cons next _ => exact False.elim (Search.no_rewrite next)
      · exact False.elim ((rooted_reachable rooted).not_nonoperation_target
          (by intro o eq; have bad := primitiveLabel_injective d (label.symm.trans eq); cases bad) mem)

/-- At a nonrewrite common token, search rootedness is exactly rootedness in
the literal common context, independently of sharing-tree presentation. -/
theorem sharing_rooted_iff (i) (q : Position C) (mode : q.1 ≠ .rewrite) :
    RootedFrom (C.expand L) i (position C L q) ↔ RootedFrom C i q := by
  have laws := deepFilling_search cert
  constructor
  · rintro ⟨n,run⟩
    obtain ⟨r,path,finish⟩ := sharing_reflect_nonrewrite_run C cert trees closed
      (rooted_initial C i) run mode
    have eq : q = r := Prod.ext (congrArg (fun x : Position (C.expand L) => x.1) finish)
      (Net.Expansion.host_injective C L (congrArg Prod.snd finish))
    exact ⟨n,eq ▸ path⟩
  · rintro ⟨n,run⟩
    refine ⟨n,?_⟩
    exact (steps_iff_trace _ _ _ _).mpr
      (((steps_iff_trace _ _ _ _).mp run).map (position C L) (step C L laws.1))
end Search.Expansion

/-- Both actual filled graphs have the same original search roots at every
nonrewrite common token; no intermediate rootedness is assumed. -/
theorem FillingWitness.sharing_rooted_iff {T : PreTemplate} (trees : T.SharingTrees)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H)
    (left : HoleFree G) (right : HoleFree H) (i : Fin I.length)
    (q : Search.Position w.context) (mode : q.1 ≠ .rewrite) :
    Search.RootedFrom G i (w.leftPosition q) ↔ Search.RootedFrom H i (w.rightPosition q) := by
  have lc : HoleFree (w.context.expand w.left) := (allLabels_iso_iff _ w.leftIso).mpr left
  have rc : HoleFree (w.context.expand w.right) := (allLabels_iso_iff _ w.rightIso).mpr right
  exact (Search.rooted_iso w.leftIso i (Search.Expansion.position w.context w.left q)).trans
    ((Search.Expansion.sharing_rooted_iff w.context w.edges trees lc i q mode).trans
      ((Search.Expansion.sharing_rooted_iff w.context (fun e => (w.edges e).converse)
        trees.converse rc i q mode).symm.trans
        (Search.rooted_iso w.rightIso i (Search.Expansion.position w.context w.right q)).symm))

end Hypernets.Copying

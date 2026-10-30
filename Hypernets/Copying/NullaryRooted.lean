import Hypernets.Copying.NullaryExecution

/-! Nullary recursive fillings preserve rootedness at every common host
position. The proof transports original search, without using contextual
equivalence or assuming a root for an intermediate semantic correction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Search.Expansion
variable {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (nullary : ∀ e h, C.edgeLabel e = primitiveLabel d (.hole h) →
      (alphabet d).signature.input (C.edgeLabel e) = [])
include nullary

/-- Original search cannot cross a nullary hole's source, or backtrack out of
one: a hole-labelled producer blocks operation-only reachability. -/
theorem nullary_boundary {i p} (rooted : RootedFrom C i p) : ¬ Boundary C p := by
  rintro (⟨mode,e,h,label,source⟩ | ⟨mode,e,h,label,target⟩)
  · have length := C.source_length e
    rw [nullary e h label] at length
    have empty : C.source e = [] := List.eq_nil_of_length_eq_zero length
    simp only [empty,List.not_mem_nil] at source
  · exact (rooted_reachable rooted).not_nonoperation_target
      (by intro o eq; have bad := primitiveLabel_injective d (label.symm.trans eq); cases bad) target

/-- Every finite filled search path from an originally rooted host position
reflects to an equally long path in the literal original context. -/
theorem nullary_reflect_run (origins : Origins C F) {i p q n}
    (rooted : RootedFrom C i p)
    (run : (machine (C.expand F)).Steps n (position C F p) q) :
    ∃ r, (machine C).Steps n p r ∧ q = position C F r := by
  generalize start : position C F p = s at run
  induction run generalizing p with
  | zero => exact ⟨p,.zero _,start.symm⟩
  | @cons n s t u first rest ih =>
    subst s
    obtain ⟨r,step,target⟩ := (reflect_or_boundary C F origins p first).resolve_right
      (nullary_boundary C nullary rooted)
    subst t
    obtain ⟨z,path,finish⟩ := ih (rooted_step rooted step) rfl
    exact ⟨z,.cons step path,finish⟩

/-- Search rootedness is identical before and after a nullary filling, at
the same original host coordinate and the same selected external input. -/
theorem nullary_rooted_iff (preserves : Preserves C F) (origins : Origins C F) (i) (q) :
    RootedFrom (C.expand F) i (position C F q) ↔ RootedFrom C i q := by
  constructor
  · rintro ⟨n,run⟩
    obtain ⟨r,path,finish⟩ := nullary_reflect_run C F nullary origins (rooted_initial C i) run
    have mode : q.1 = r.1 := congrArg (fun x : Position (C.expand F) => x.1) finish
    have eq : q = r := Prod.ext mode
      (Net.Expansion.host_injective C F (congrArg Prod.snd finish))
    exact ⟨n,eq ▸ path⟩
  · rintro ⟨n,run⟩
    refine ⟨n,?_⟩
    exact (steps_iff_trace _ _ _ _).mpr
      (((steps_iff_trace _ _ _ _).mp run).map (position C F) (step C F preserves))
end Search.Expansion

/-- A nullary paired recursive filling transports actual rootedness in both
directions, including when its common token is internal. Hole freedom of one
actual endpoint forces every original shallow hole to have its true nullary
interface; unchanged and rebuilt box corollas retain their original search. -/
theorem FillingWitness.nullary_rooted_iff {T : PreTemplate} (none : T.NoInputs)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H) (left : HoleFree G)
    (i : Fin I.length) (q : Search.Position w.context) :
    Search.RootedFrom G i (w.leftPosition q) ↔ Search.RootedFrom H i (w.rightPosition q) := by
  have closed : HoleFree (w.context.expand w.left) := (allLabels_iso_iff _ w.leftIso).mpr left
  have nullary : ∀ e h, w.context.edgeLabel e = primitiveLabel d (.hole h) →
      (alphabet d).signature.input (w.context.edgeLabel e) = [] := by
    intro e h label
    exact none ((w.edges e).relation_at_hole label closed)
  have laws := deepFilling_search w.edges
  exact (Search.rooted_iso w.leftIso i (Search.Expansion.position w.context w.left q)).trans
    ((Search.Expansion.nullary_rooted_iff w.context w.left nullary laws.1 laws.2.2.1 i q).trans
      ((Search.Expansion.nullary_rooted_iff w.context w.right nullary laws.2.1 laws.2.2.2 i q).symm.trans
        (Search.rooted_iso w.rightIso i (Search.Expansion.position w.context w.right q)).symm))

end Hypernets.Copying

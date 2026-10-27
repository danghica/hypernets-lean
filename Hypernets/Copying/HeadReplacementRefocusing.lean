import Hypernets.Copying.SearchHistory

/-! Refocusing for replacement of an operation head, from actual search history. -/
namespace Hypernets.Copying.Search
open Graph
variable {d I O} {G : Hypernet d I O} {i : Fin I.length}

/-- A search visit cannot repeat before a reachable rewrite normal form. -/
theorem Visit.no_earlier_cycle {n k r p v z} (visit : Visit G i n p v)
    (rest : (machine G).Steps k p (.search,v)) (positive : 0 < k)
    (finish : (machine G).Steps r (.search,v) z) (mode : z.1 = .rewrite) : False := by
  obtain ⟨a,b,_,_,tail⟩ := visit
  have terminal : Terminal (Step G) z := by
    intro q step
    have eq : z = (.rewrite,z.2) := Prod.ext mode rfl
    rw [eq] at step
    exact no_rewrite step
  have equal := (Trace.terminal_unique (R := Step G) (fun h h' => deterministic h h')
    ((steps_iff_trace G _ _ _).mp ((tail.append rest).append finish))
    ((steps_iff_trace G _ _ _).mp finish) terminal terminal).2
  omega

/-- Any search interaction away from the replaced head transports into the original host. -/
theorem replace_step {e} (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
    ((alphabet d).signature.output (G.edgeLabel e))) {p q : Position G}
    (step : Step G p q)
    (away : ∀ b primitive, G.edgeLabel b = primitiveLabel d primitive →
      ((p.1 = .search ∧ p.2 ∈ G.source b) ∨
       (p.1 = .backtrack ∧ ∃ j : Nat, (G.target b)[j]? = some p.2)) → b ≠ e) :
    Step (G.plug e A) (p.1,Net.Replacement.host G e A p.2)
      (q.1,Net.Replacement.host G e A q.2) := by
  cases step with
  | search b primitive v q label mem result =>
    have ne := away b primitive label (.inl ⟨rfl,mem⟩)
    apply Step.search (G := G.plug e A) (.inl ⟨b,ne⟩) primitive _ _ label
    · exact List.mem_map_of_mem mem
    · change enter primitive _ ((G.target b).map _) = _
      rw [enter_map,result]; rfl
  | backtrack b o root v j q label source bound arg result =>
    have ne := away b (.operation o) label (.inr ⟨rfl,j,arg⟩)
    apply Step.backtrack (G := G.plug e A) (.inl ⟨b,ne⟩) o (Net.Replacement.host G e A root) _ j _ label
    · change (G.source b).map _ = _; rw [source]; rfl
    · exact bound
    · change ((G.target b).map _)[j]? = _; rw [List.getElem?_map,arg]; rfl
    · change resume o _ ((G.target b).map _) j = _; rw [resume_map,result]; rfl

/-- Replay precisely the pre-head prefix; it has never used the replaced operation. -/
theorem replace_prefix {e o v} (_label : G.edgeLabel e = primitiveLabel d (.operation o))
    (source : G.source e = [v])
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)))
    {n k r p z} (initialRun : (machine G).Steps n (.search,.input i) p)
    (rest : (machine G).Steps k p (.search,v))
    (finish : (machine G).Steps r (.search,v) z) (mode : z.1 = .rewrite) :
    (machine (G.plug e A)).Steps k (p.1,Net.Replacement.host G e A p.2)
      (.search,Net.Replacement.host G e A v) := by
  induction k generalizing n p with
  | zero => cases rest; exact .zero _
  | succ k ih =>
    have avoid : ¬ Visit G i n p v := fun visit => visit.no_earlier_cycle rest (by omega) finish mode
    cases rest with
    | cons step tail =>
      refine .cons (replace_step A step ?_) (ih (initialRun.append (.cons step (.zero _))) tail)
      intro b primitive bl used eq
      subst b
      rcases used with ⟨pmode,mem⟩ | ⟨pmode,j,arg⟩
      · have same : p.2 = v := by simpa [source] using mem
        have eq : p = (.search,v) := Prod.ext pmode same
        subst p
        exact avoid (Visit.current initialRun)
      · exact avoid (((history initialRun).1.parent source (List.mem_of_getElem? arg)).2)

/-- Replacing a single operation edge preserves rootedness at its unchanged source port. -/
theorem replacement_rooted {e o v} (head : MatchEmbedding.HeadAt G v e (.operation o))
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)))
    (root : RootedFrom G i (.rewrite,v)) :
    RootedFrom (G.plug e A) i (.search,Net.Replacement.host G e A v) := by
  obtain ⟨n,run⟩ := root
  obtain ⟨a,b,_,_,initialRun,finish⟩ := revisit run (by intro h; cases h)
  exact ⟨a,replace_prefix head.1 (operation_source head.1 head.2) A
    (n := 0) (.zero _) initialRun finish rfl⟩
end Hypernets.Copying.Search

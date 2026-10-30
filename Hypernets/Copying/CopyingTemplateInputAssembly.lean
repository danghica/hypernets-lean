import Hypernets.Copying.CopyingTemplateResidualExpansion
import Hypernets.Copying.TemplateConsumption

/-! Lift the two actual non-distinguished-input prefixes and their original
copying/sharing residual into an arbitrary original recursive specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Combined

/-- The actual one-search/one-copy prefix is preserved by simultaneous graph
expansion, including the exact unchanged host attachment coordinate. -/
theorem expanded_entry {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length)
    (others : ∀ b, b ≠ e → F b = K b)
    (request : Search.Step (F e) (.search,.input i) (.rewrite,.input i))
    (step : Rewrite (F e) (.input i) (K e) (.input i)) :
    (Combined.machine d I O).Steps 2
      ⟨C.expand F,(.search,Net.Expansion.host C F (C.sourcePort e i))⟩
      ⟨C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩ :=
  .cons (.search _ (Search.expand_insert C F e request))
    (.cons (.rewrite (.expand C F K e others step)) (.zero _))

/-- No original filling outside the entered component is discarded. The
constructed residual has the actual host token and exact two-transition
prefixes on both sides, and sharing is used only for its proved correction. -/
theorem entry_diamond (S : Specimen template Specimens.allContexts)
    (e : S.context.Edge)
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (token : S.token = (.search,S.context.sourcePort e i))
    (A B : Hypernet S.depth ((alphabet S.depth).signature.input (S.context.edgeLabel e))
      ((alphabet S.depth).signature.output (S.context.edgeLabel e)))
    (leftRequest : Search.Step (S.left e) (.search,.input i) (.rewrite,.input i))
    (rightRequest : Search.Step (S.right e) (.search,.input i) (.rewrite,.input i))
    (leftStep : Rewrite (S.left e) (.input i) A (.input i))
    (rightStep : Rewrite (S.right e) (.input i) B (.input i))
    (residual : Residual A (.input i) B (.input i)) :
    ∃ s t, StateClass.machine.Steps 2 (StateClass.ofState S.leftState) s ∧
      StateClass.machine.Steps 2 (StateClass.ofState S.rightState) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Equiv CostOrder.exact) (StateClass.machine.Equiv CostOrder.exact) s t := by
  let C := S.context
  let F := OperationalSafety.replace C S.left e A
  let K := OperationalSafety.replace C S.right e B
  have build (X Y : Hypernet S.depth ((alphabet S.depth).signature.input (C.edgeLabel e))
      ((alphabet S.depth).signature.output (C.edgeLabel e))) (leftEq : F e = X) (rightEq : K e = Y)
      (ls : Rewrite (S.left e) (.input i) X (.input i))
      (rs : Rewrite (S.right e) (.input i) Y (.input i))
      (p : Residual X (.input i) Y (.input i)) :
      ∃ s t, StateClass.machine.Steps 2 (StateClass.ofState S.leftState) s ∧
        StateClass.machine.Steps 2 (StateClass.ofState S.rightState) t ∧
        (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
          (StateClass.machine.Equiv CostOrder.exact) (StateClass.machine.Equiv CostOrder.exact) s t := by
    subst X; subst Y
    have leftOthers (b) (ne : b ≠ e) : S.left b = F b :=
      (OperationalSafety.replace_other C S.left e A b ne).symm
    have rightOthers (b) (ne : b ≠ e) : S.right b = K b :=
      (OperationalSafety.replace_other C S.right e B b ne).symm
    have other (b) (ne : b ≠ e) : FillingWitness template (F b) (K b) := by
      rw [← leftOthers b ne,← rightOthers b ne]
      exact FillingWitness.of_edge (S.edges b) S.free
    let whole := Residual.expandSelected C F K e p other
    have lrun := expanded_entry C S.left F e i leftOthers leftRequest ls
    have rrun := expanded_entry C S.right K e i rightOthers rightRequest rs
    have closed : HoleFree (C.expand F) :=
      rewrite_holeFree (.expand C S.left F e leftOthers ls) S.left_closed
    have typed : (C.expand F).vertexLabel (Net.Expansion.host C F (C.sourcePort e i)) = .term := by
      have h := S.term
      rw [token] at h
      exact (Net.Expansion.host_label C F (C.sourcePort e i)).trans h
    refine ⟨StateClass.ofState ⟨S.depth,C.expand F,(.search,Net.Expansion.host C F (C.sourcePort e i))⟩,
      StateClass.ofState ⟨S.depth,C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩,?_,?_,?_⟩
    · have initial : S.leftState = ⟨S.depth,C.expand S.left,(.search,Net.Expansion.host C S.left (C.sourcePort e i))⟩ := by
        simp only [Specimen.leftState,token,Search.Expansion.position,C]
      rw [initial]
      exact StateClass.project_run (run_unbounded lrun)
    · have initial : S.rightState = ⟨S.depth,C.expand S.right,(.search,Net.Expansion.host C S.right (C.sourcePort e i))⟩ := by
        simp only [Specimen.rightState,token,Search.Expansion.position,C]
      rw [initial]
      exact StateClass.project_run (run_unbounded rrun)
    · exact whole.quasi_equiv closed typed
  exact build A B (OperationalSafety.replace_selected C S.left e A)
    (OperationalSafety.replace_selected C S.right e B) leftStep rightStep residual

/-- The remaining local obligation for multi-input copying: an actual
request/compute prefix on each side and a certified original residual. -/
def OtherEntries : Prop :=
  ∀ {d I O} {G H : Hypernet d I O}, Pair G H →
    ∀ i : Fin I.length, 0 < i.val →
      ∃ A B : Hypernet d I O,
        Search.Step G (.search,.input i) (.rewrite,.input i) ∧
        Search.Step H (.search,.input i) (.rewrite,.input i) ∧
        Rewrite G (.input i) A (.input i) ∧ Rewrite H (.input i) B (.input i) ∧
        Nonempty (Residual A (.input i) B (.input i))

/-- Case II handles the distinguished input with its exact 2/0 costs. Case III
handles every other input with exact 2/2 costs and the independently completed
sharing correction. The local diagrams, rather than a semantic equivalence
assumption, are the only argument to this assembly theorem. -/
theorem inputSafe_of_otherEntries (entries : OtherEntries) (Q P : CostOrder)
    (selectedCost : Q.rel 2 0) :
    (Specimens.system template Specimens.allContexts template_outputClosed).InputSafe Q P := by
  intro S _ _ mode entering
  change S.token.1 = .search at mode
  obtain ⟨e,h,label,mem⟩ := entering
  have pair := (S.edges e).relation_at_hole label S.left_closed
  obtain ⟨i,eq⟩ := (S.context.mem_source_iff_port e S.token.2).mp mem
  have token : S.token = (.search,S.context.sourcePort e i) := Prod.ext mode eq.symm
  by_cases first : i.val = 0
  · obtain ⟨D,search,away,run,rightEq⟩ := consume_selected_allContexts S e pair i first token
    right; left
    refine ⟨D,1,0,Or.inr ⟨search,away⟩,selectedCost,run,?_⟩
    change StateClass.machine.Steps 0 (StateClass.ofState S.rightState) (StateClass.ofState D.rightState)
    rw [rightEq]
    exact .zero _
  · obtain ⟨A,B,lq,rq,ls,rs,⟨residual⟩⟩ := entries pair i (by omega)
    obtain ⟨s,t,lrun,rrun,quasi⟩ := entry_diamond S e i token A B lq rq ls rs residual
    right; right
    refine ⟨1,1,s,t,Q.refl 2,lrun,rrun,?_⟩
    intro lroot rroot
    obtain ⟨D,mode,lroot',rroot',left,right⟩ := quasi lroot rroot
    refine ⟨D,mode,lroot',rroot',?_,?_⟩
    · exact ⟨left.1.mono (fun {n m} eq => by cases eq; exact P.refl n),
        left.2.mono (fun {n m} eq => by cases eq; exact P.refl n)⟩
    · exact ⟨right.1.mono (fun {n m} eq => by cases eq; exact P.refl n),
        right.2.mono (fun {n m} eq => by cases eq; exact P.refl n)⟩

end Hypernets.Copying.CopyingTemplate

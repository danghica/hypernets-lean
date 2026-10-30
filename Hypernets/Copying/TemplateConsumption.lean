import Hypernets.Copying.OperationalInputSafety

/-! Consume one actual entered template component after a proved finite
search prefix and its original compute step. This is a generic graph
construction, retaining all unrelated shallow and deep template occurrences. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TemplateConsumption
open Graph Combined OperationalSafety

/-- The exact original right component moves into the common context after
one compute transition. The selected token becomes settled; the right
endpoint takes zero steps. Every semantic hypothesis is an actual finite
search trace or an original whole-graph rewrite, rather than equivalence. -/
theorem consume {T : PreTemplate} {Allowed} (S : Specimen T Allowed)
    (e : S.context.Edge)
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (token : S.token = (.search,S.context.sourcePort e i))
    (searchCount : Nat)
    (trace : Trace (Search.Step (S.left e)) (.search,.input i) (.rewrite,.input i) searchCount)
    (rewrite : Rewrite (S.left e) (.input i) (S.right e) (.input i))
    (rightFree : FocusFree (S.right e))
    (allowed : Allowed S.depth (S.context.plug e (S.right e))) :
    ∃ D : Specimen T Allowed,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps (searchCount+1)
        (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState S.rightState := by
  classical
  let C := S.context
  let H := S.right e
  let K := replace C S.left e H
  have rightClosed : HoleFree H := fun x => S.right_closed ⟨e,x⟩
  have selectedStep : Rewrite (C.expand S.left)
      (Net.Expansion.host C S.left (C.sourcePort e i)) (C.expand K)
      (Net.Expansion.host C K (C.sourcePort e i)) := by
    have aux (H') (eq : K e = H')
        (step : Rewrite (S.left e) (.input i) H' (.input i)) :
        Rewrite (C.expand S.left) (Net.Expansion.host C S.left (C.sourcePort e i))
          (C.expand K) (Net.Expansion.host C K (C.sourcePort e i)) := by
      subst H'
      exact .expand C S.left K e
        (fun b ne => (replace_other C S.left e H b ne).symm) step
    exact aux H (replace_selected C S.left e H) rewrite
  have closedK : HoleFree (C.expand K) := rewrite_holeFree selectedStep S.left_closed
  have run : (Combined.machine S.depth [.term] []).Steps (searchCount+1)
      ⟨C.expand S.left,(.search,Net.Expansion.host C S.left (C.sourcePort e i))⟩
      ⟨C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩ := by
    have traversal := search_run (C.expand S.left)
      (trace.map (fun q => (q.1,Net.Expansion.insert C S.left e q.2))
        (Search.expand_insert C S.left e))
    exact traversal.append (.cons (.rewrite selectedStep) (.zero _))
  obtain ⟨leftIso,leftPoint⟩ := remaining_iso C S.left e H
  have rightData : ∃ f : DeepIso ((C.plug e H).expand (remaining C S.right e H))
      (C.expand S.right), ∀ v, Port.map f.vertices.toFun
      (Net.Expansion.host (C.plug e H) (remaining C S.right e H)
        (Net.Replacement.host C e H v)) = Net.Expansion.host C S.right v := by
    have family : remaining C S.right e H = Net.ExpansionPeel.rest C S.right e := by
      funext x; cases x <;> rfl
    rw [family]
    exact ⟨DeepIso.ofIso (Net.ExpansionPeel.iso C S.right e),
      Net.ExpansionPeel.map_host C S.right e⟩
  obtain ⟨rightIso,rightPoint⟩ := rightData
  let D : Specimen T Allowed := {
    depth := S.depth
    context := C.plug e H
    allowed := allowed
    free := focusFree_closed (.shallow C e) H S.free rightFree
    left := remaining C S.left e H
    right := remaining C S.right e H
    edges := remaining_edges C S.left S.right e H S.edges
    left_closed := (allLabels_iso_iff _ leftIso).mpr closedK
    right_closed := (allLabels_iso_iff _ rightIso).mpr S.right_closed
    token := (.search,Net.Replacement.host C e H (C.sourcePort e i))
    term := by
      have typed := S.term
      rw [token] at typed
      change C.vertexLabel (C.sourcePort e i) = .term at typed
      have hostLabel (v : C.Vertex) :
          (C.plug e H).vertexLabel (Net.Replacement.host C e H v) = C.vertexLabel v := by
        cases v <;> rfl
      exact (hostLabel _).trans typed }
  have l : StateClass.ofState D.leftState =
      StateClass.ofState ⟨S.depth,C.expand K,
        (.search,Net.Expansion.host C K (C.sourcePort e i))⟩ :=
    Quotient.sound (.iso (.lift ⟨leftIso,rfl,leftPoint _⟩))
  have r : StateClass.ofState D.rightState =
      StateClass.ofState ⟨S.depth,C.expand S.right,
        (.search,Net.Expansion.host C S.right (C.sourcePort e i))⟩ :=
    Quotient.sound (.iso (.lift ⟨rightIso,rfl,rightPoint _⟩))
  refine ⟨D,rfl,consumed_not_entering C e H rightClosed i,?_,?_⟩
  · rw [l]
    have start : S.leftState = ⟨S.depth,C.expand S.left,
        (.search,Net.Expansion.host C S.left (C.sourcePort e i))⟩ := by
      simp only [Specimen.leftState,token,Search.Expansion.position,C]
    rw [start]
    exact StateClass.project_run (run_unbounded run)
  · have finish : S.rightState = ⟨S.depth,C.expand S.right,
        (.search,Net.Expansion.host C S.right (C.sourcePort e i))⟩ := by
      simp only [Specimen.rightState,token,Search.Expansion.position,C]
    rw [finish]
    exact r

end Hypernets.Copying.TemplateConsumption

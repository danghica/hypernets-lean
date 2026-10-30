import Hypernets.Copying.MinimalContractionSpine

/-! An actual finite remote-copy prefix realizes a complete selected term
spine in the original context. Its sibling wires become ordered inputs, while
both the original token and the exact reached hole input remain fixed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.Remote
open Graph Opening

/-- Every finite sharing prefix ending immediately before a terminal edge has
an injective selected-spine occurrence, with no unused sibling subtree added. -/
theorem prefix_spine {d I O} (C : Hypernet d I O) {a last stop : C.Edge} {n : Nat}
    (route : Trace (CopyTrace.Hop C) a last n)
    (finalHop : CopyTrace.Hop C last stop) (terminal : Terminal (CopyTrace.Hop C) stop)
    {v w : C.Vertex} (initial : v ∈ C.source a) (finalTarget : w ∈ C.target last) :
    ∃ (orientation : Fin (n+1) → Bool)
      (f : Occurrence (ContractionSpine.atDepth .term n orientation d) C),
      f.ports (.input ⟨0,by simp⟩) = v ∧ f.ports (.output 0) = w ∧
      (∀ e, Trace (CopyTrace.Hop C) a (f.edges e) e.val) ∧
      (∀ e, Trace (CopyTrace.Hop C) (f.edges e) stop (n-e.val+1)) := by
  classical
  obtain ⟨edges,first,lastEdge,adj,pre,suffix⟩ := route.indexed
  have tails (e : Fin (n+1)) : Trace (CopyTrace.Hop C) (edges e) stop (n-e.val+1) :=
    CopyTrace.snoc (suffix e) finalHop
  have inj : Function.Injective edges := by
    intro i j eq
    have len := (Trace.terminal_unique (R := CopyTrace.Hop C)
      (fun h h' => CopyTrace.hop_functional h h') (tails i) (eq ▸ tails j) terminal terminal).2
    apply Fin.ext
    have bi := i.isLt
    have bj := j.isLt
    omega
  have forward (e : Fin (n+1)) : CopyTrace.ForwardLabel d (C.edgeLabel (edges e)) := by
    have tail := tails e
    cases tail with
    | step hop _ => exact hop.1
  have one (e : Fin (n+1)) : (C.target (edges e)).length = 1 := by
    rw [C.target_length,CopyTrace.forward_output (forward e)]
    rfl
  let node (e : Fin (n+1)) : C.Vertex :=
    C.targetPort (edges e) ⟨0,by rw [← C.target_length,one]; decide⟩
  have targets (e) : C.target (edges e) = [node e] := by
    apply List.ext_getElem (by simpa using one e)
    intro j hj _
    have zero : j = 0 := by have := one e; omega
    subst j
    rfl
  let path (j : Fin (n+2)) : C.Vertex :=
    if z : j.val = 0 then v else node ⟨j.val-1,by omega⟩
  have pathFirst : path ⟨0,by omega⟩ = v := by simp [path]
  have pathNext (e : Fin (n+1)) : path ⟨e.val+1,by omega⟩ = node e := by simp [path]
  have selected (e : Fin (n+1)) : path ⟨e.val,by omega⟩ ∈ C.source (edges e) := by
    by_cases z : e.val = 0
    · have eq : e = ⟨0,by omega⟩ := Fin.ext z
      rw [eq]
      simpa only [pathFirst,first] using initial
    · let prev : Fin n := ⟨e.val-1,by omega⟩
      obtain ⟨u,produced,consumed⟩ := (adj prev).2
      have after : prev.succ = e := Fin.ext (by simp [prev]; omega)
      rw [after] at consumed
      rw [targets] at produced
      have eq := List.mem_singleton.mp produced
      have before : prev.castSucc = (⟨e.val-1,by omega⟩ : Fin (n+1)) := Fin.ext rfl
      rw [eq,before] at consumed
      simpa only [path,z,↓reduceDIte] using consumed
  have labels (e : Fin (n+1)) : C.edgeLabel (edges e) = primitiveLabel d (.contraction .term) := by
    rcases forward e with contr | weak
    · exact contr
    · have len := C.source_length (edges e)
      rw [weak,primitive_input] at len
      have empty : C.source (edges e) = [] := List.length_eq_zero_iff.mp len
      have mem := selected e
      rw [empty] at mem
      exact False.elim (List.not_mem_nil mem)
  have forms (e : Fin (n+1)) : ∃ right other,
      C.source (edges e) = CopyRule.selectedSources right (path ⟨e.val,by omega⟩) other := by
    apply CopyRule.selected_sources_exists _ (selected e)
    rw [C.source_length,labels,primitive_input]
    rfl
  let orientation (e) := Classical.choose (forms e)
  let sides (e) := Classical.choose (Classical.choose_spec (forms e))
  have sources (e : Fin (n+1)) : C.source (edges e) =
      if orientation e then [sides e,path ⟨e.val,by omega⟩] else [path ⟨e.val,by omega⟩,sides e] :=
    Classical.choose_spec (Classical.choose_spec (forms e))
  let f := ContractionSpine.occurrence C .term n orientation edges path sides inj labels sources
    (fun e => (targets e).trans (congrArg (fun u => [u]) (pathNext e).symm))
  refine ⟨orientation,f,pathFirst,?_,pre,tails⟩
  change path ⟨n+1,by omega⟩ = w
  rw [pathNext ⟨n,by omega⟩]
  rw [← lastEdge,targets] at finalTarget
  exact (List.mem_singleton.mp finalTarget).symm

end Hypernets.Copying.CopyingTemplate.Remote

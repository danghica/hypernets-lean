import Hypernets.Copying.ContractionSpineEmbedding
import Hypernets.Copying.IndexedTrace
import Hypernets.Copying.CopySuccessorLocalMatch

/-! Every selected input of a finite contraction tree admits a smaller
complete match containing precisely its forward spine. Unused branches are
boundary attachments, not assumptions about the surrounding graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree
open Graph Opening
variable {s : ShareSort} {m : Nat} (T : ContractionTree s m)

/-- Realize an arbitrary sharing tree in the requested copying alphabet. -/
def atDepth (d : Nat) : Hypernet d (List.replicate m s.wire) [s.wire] :=
  T.net.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

/-- A nonempty source selects a contraction, never a weakening. -/
theorem contraction_of_source {e : T.net.Edge} {v} (source : v ∈ T.net.source e) :
    T.net.edgeLabel e = .contraction s := by
  rcases T.labels e with weak | contraction
  · have len := T.net.source_length e
    rw [weak] at len
    have empty := List.length_eq_zero_iff.mp len
    rw [empty] at source
    exact False.elim (List.not_mem_nil source)
  · exact contraction

/-- Every target list contains its unique ordered output port. -/
theorem target_port (e : T.net.Edge) :
    T.net.target e = [T.net.targetPort e ⟨0,by rw [← T.net.target_length,T.target_single]; decide⟩] := by
  have len := T.target_single e
  apply List.ext_getElem (by simpa using len)
  intro j hj _
  have zero : j = 0 := by omega
  subst j
  rfl

/-- Exact minimal-spine extraction, with original selected-input and output
coordinates and a counted original ancestry witness for every retained edge. -/
theorem minimal_spine (d : Nat) (i : Fin (List.replicate m s.wire).length) :
    ∃ (n : Nat) (orientation : Fin (n+1) → Bool)
      (f : Occurrence (ContractionSpine.atDepth s n orientation d) (T.atDepth d)),
      f.ports (.input ⟨0,by simp⟩) = .input i ∧
      f.ports (.output 0) = .output 0 ∧
      ∃ a, Port.input i ∈ T.net.source a ∧
        ∀ e, Trace T.net.Adjacent a (f.edges e) e.val := by
  classical
  obtain ⟨a,n,initial,route⟩ := T.input_reaches_root i
  obtain ⟨edges,first,last,adj,pre,suffix⟩ := route.indexed
  have inj := Trace.indexed_injective (R := T.net.Adjacent)
    (fun h h' => T.adjacent_functional h h') T.root_terminal edges suffix
  let node (e : Fin (n+1)) : T.net.Vertex :=
    T.net.targetPort (edges e) ⟨0,by rw [← T.net.target_length,T.target_single]; decide⟩
  have targets (e) : T.net.target (edges e) = [node e] := T.target_port (edges e)
  let path (j : Fin (n+2)) : T.net.Vertex :=
    if z : j.val = 0 then .input i else node ⟨j.val-1,by omega⟩
  have path_first : path ⟨0,by omega⟩ = .input i := by simp [path]
  have path_next (e : Fin (n+1)) : path ⟨e.val+1,by omega⟩ = node e := by
    simp [path]
  have selected (e : Fin (n+1)) : path ⟨e.val,by omega⟩ ∈ T.net.source (edges e) := by
    by_cases z : e.val = 0
    · have eq : e = ⟨0,by omega⟩ := Fin.ext z
      rw [eq]
      simpa only [path_first,first] using initial
    · let prev : Fin n := ⟨e.val-1,by omega⟩
      obtain ⟨v,produced,consumed⟩ := adj prev
      have after : prev.succ = e := Fin.ext (by simp [prev]; omega)
      rw [after] at consumed
      rw [targets] at produced
      have eq := List.mem_singleton.mp produced
      have before : prev.castSucc = (⟨e.val-1,by omega⟩ : Fin (n+1)) := Fin.ext rfl
      rw [eq,before] at consumed
      simpa only [path,z,↓reduceDIte] using consumed
  have labels (e : Fin (n+1)) : T.net.edgeLabel (edges e) = .contraction s :=
    T.contraction_of_source (selected e)
  have forms (e : Fin (n+1)) : ∃ right other,
      T.net.source (edges e) = CopyRule.selectedSources right (path ⟨e.val,by omega⟩) other := by
    apply CopyRule.selected_sources_exists _ (selected e)
    rw [T.net.source_length,labels]
    rfl
  let orientation (e) := Classical.choose (forms e)
  let sides (e) := Classical.choose (Classical.choose_spec (forms e))
  have sources (e : Fin (n+1)) : T.net.source (edges e) =
      if orientation e then [sides e,path ⟨e.val,by omega⟩] else [path ⟨e.val,by omega⟩,sides e] :=
    Classical.choose_spec (Classical.choose_spec (forms e))
  let f := ContractionSpine.occurrence (T.atDepth d) s n orientation edges path sides inj
    (fun e => congrArg (primitiveLabel d) (labels e)) sources
    (fun e => (targets e).trans (congrArg (fun v => [v]) (path_next e).symm))
  refine ⟨n,orientation,f,?_,?_,a,initial,?_⟩
  · exact path_first
  · change path ⟨n+1,by omega⟩ = Port.output 0
    rw [path_next ⟨n,by omega⟩]
    have member := T.root_output
    rw [← last,targets] at member
    exact (List.mem_singleton.mp member).symm
  · exact pre

end Hypernets.Copying.ContractionTree

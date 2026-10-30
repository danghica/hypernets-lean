import Hypernets.Copying.ContractionAlgebraLaws
import Hypernets.Copying.CopyingTemplateEntry

/-! Entering any term input of an actual sharing tree requests copying in
exactly one original search step, independently of the tree presentation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

/-- A weakening has no input; hence the unique consumer of a tree input is
an actual contraction, regardless of the number of unused predecessor leaves. -/
theorem ContractionTree.request {m} (T : ContractionTree .term m) (d : Nat)
    (i : Fin (List.replicate m Wire.term).length) :
    Search.Step (T.atDepth d) (.search,.input i) (.rewrite,.input i) := by
  obtain ⟨e,source⟩ := ((T.atDepth d).source_coverage (.input i)).mpr (by simp [Port.IsOutput])
  have label : (T.atDepth d).edgeLabel e = primitiveLabel d (.contraction .term) := by
    rcases (T.sharingTreeGraph d).labels e with weak | contr
    · have len := (T.atDepth d).source_length e
      rw [weak,primitive_input] at len
      have empty : (T.atDepth d).source e = [] := List.length_eq_zero_iff.mp len
      simp [empty] at source
    · exact contr
  exact .search e (.contraction .term) _ _ label source rfl

/-- Independent carrier names and either sharing sort are handled through the
literal pair's original ordered interface, with term typing excluding atom entry. -/
theorem SharingTreePair.request {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H)
    (i : Fin I.length) (typed : I[i] = .term) :
    Search.Step G (.search,.input i) (.rewrite,.input i) := by
  cases pair with
  | @trees s m T U G H left right =>
    have sort : s = .term := by
      have wire : s.wire = .term := (List.getElem_replicate i.isLt).symm.trans typed
      cases s
      · rfl
      · cases wire
    subst s
    exact (Search.ofBoundaryIso (BoundaryIso.ofDeepIso left.symm)).step (T.request d i)

/-- The same entered original component on both sides requests rewriting at
the unchanged common host port. No remote-token premise is used. -/
theorem Specimen.sharing_requests {T : PreTemplate} {Allowed}
    (S : Specimen T Allowed) (trees : T.SharingTrees)
    (mode : S.token.1 = .search) (entering : S.Entering) :
    let D := S.relocate (.rewrite,S.token.2) S.term
    StateClass.machine.step (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.machine.step (StateClass.ofState S.rightState) (StateClass.ofState D.rightState) := by
  obtain ⟨e,h,label,mem⟩ := entering
  have rel := (S.edges e).relation_at_hole label S.left_closed
  obtain ⟨i,port⟩ := (S.context.mem_source_iff_port e S.token.2).mp mem
  have typed : ((alphabet S.depth).signature.input (S.context.edgeLabel e))[i] = .term :=
    (S.context.sourcePort_label e i).symm.trans (port ▸ S.term)
  have left := Search.expand_insert S.context S.left e ((trees rel).request i typed)
  have right := Search.expand_insert S.context S.right e ((trees rel).converse.request i typed)
  have token : S.token = (.search,S.context.sourcePort e i) := Prod.ext mode port.symm
  constructor
  · have actual : Step S.leftState.2 (S.relocate (.rewrite,S.token.2) S.term).leftState.2 := by
      simpa only [Specimen.leftState,Specimen.relocate,Search.Expansion.position,Net.Expansion.insert,token] using Step.search _ left
    exact StateClass.project (.lift actual)
  · have actual : Step S.rightState.2 (S.relocate (.rewrite,S.token.2) S.term).rightState.2 := by
      simpa only [Specimen.rightState,Specimen.relocate,Search.Expansion.position,Net.Expansion.insert,token] using Step.search _ right
    exact StateClass.project (.lift actual)

end Hypernets.Copying

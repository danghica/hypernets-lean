import Hypernets.Copying.CopyingTemplateForwardBarrier
import Hypernets.Copying.CopyPayloadRigidity

/-! The payload reached after entering a shallow copying source is the actual
copyable payload of that component, including its full recursive box body.
Functional copy resolution rules out escaping into an unrelated payload. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Opening Search.Expansion

/-- Every original source input resolves to an actual complete occurrence of
its original copyable payload, in a canonical outer representation only. -/
theorem Pair.input_payload {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) (i : Fin I.length) :
    ∃ k h, ∃ V : Hypernet d [.term] (environmentInterface k h),
      ∃ normal : CopyRule.NormalForm V, FocusFree V ∧
      ∃ payload : Occurrence V G, ∃ m,
        CopyTrace.Resolves G (.input i) (payload.edges normal.head) normal.primitive (m+1) := by
  cases pair with
  | witness f literal g =>
    cases literal with
    | copy tree A copyable free =>
      obtain ⟨V,⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
      let inA := Occurrence.ofIso iso.symm
      let payload := (inA.comp (Occurrence.serialRight (CopyRule.tree tree d) A)).comp (Occurrence.ofIso f.symm)
      have head := inA.matchEmbedding.head normal.head_at
      obtain ⟨m,resolve⟩ := CopyRule.before_resolves_head tree A copyable i head
      have mapped := CopyTrace.resolves_map (MatchEmbedding.ofDeepIso f.symm) resolve
      refine ⟨_,_,V,normal,(allLabels_iso_iff _ iso).mp free,payload,m,?_⟩
      exact mapped

namespace Remote
/-- A successful actual suffix after first shallow entry ends at that same
component's complete normalized payload. Every payload edge keeps that exact
original hole owner; nested bodies are preserved through full-label occurrence. -/
theorem shallow_payload {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {hole : C.Edge} {name}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (L hole).Edge} (source : Port.input i ∈ (L hole).source entry)
    {last : (C.expand L).Edge} {n p}
    (suffix : Trace (CopyTrace.Hop (C.expand L)) ⟨hole,entry⟩ last n)
    (lastLabel : (C.expand L).edgeLabel last = primitiveLabel d p)
    (kind : CopyTrace.PayloadHead p) :
    ∃ k h, ∃ V : Hypernet d [.term] (environmentInterface k h),
      ∃ normal : CopyRule.NormalForm V, FocusFree V ∧
      ∃ payload : Occurrence V (C.expand L),
        payload.edges normal.head = last ∧ normal.primitive = p ∧
        (∀ e, (payload.edges e).1 = hole) ∧
        ∃ m, n = m+1 := by
  have pair := (cert hole).relation_at_hole label closed
  obtain ⟨k,h,V,normal,free,payload,m,resolve⟩ := pair.input_payload i
  let expanded := payload.comp (Occurrence.expand C L hole)
  have canonical := CopyTrace.resolves_map (MatchEmbedding.expand C L hole) resolve
  have actual : CopyTrace.Resolves (C.expand L)
      (Net.Expansion.insert C L hole (.input i)) last p n :=
    ⟨⟨hole,entry⟩,List.mem_map_of_mem source,suffix,lastLabel,kind⟩
  have same := CopyTrace.resolves_unique canonical actual
  exact ⟨k,h,V,normal,free,expanded,same.1,same.2.1,fun _ => rfl,m,same.2.2.symm⟩
end Remote
end Hypernets.Copying.CopyingTemplate

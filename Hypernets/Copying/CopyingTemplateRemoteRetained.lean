import Hypernets.Copying.CopyingTemplateRemoteClassification
import Hypernets.Copying.CopyingTemplateLeftLabels

/-! A resolved copy path whose actual payload head remains outside shallow
holes cannot pass through a shallow copying component. This proves retention
for every edge of its selected spine, without assuming unrelated tree siblings
are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.Remote
open Graph Opening Search.Expansion

/-- Every prefix of the actual successful copy resolution avoids shallow
holes when its complete payload has a non-hole original head owner. -/
theorem trace_prefix_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand L))
    (last : ∀ name, C.edgeLabel (payload.edges normal.head).1 ≠ primitiveLabel d (.hole name))
    {a : (C.expand L).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand L)) a (payload.edges normal.head) n)
    (initial : ∀ name, C.edgeLabel a.1 ≠ primitiveLabel d (.hole name)) :
    ∀ {b m}, Trace (CopyTrace.Hop (C.expand L)) a b m →
      ∀ name, C.edgeLabel b.1 ≠ primitiveLabel d (.hole name) := by
  have kind : CopyTrace.PayloadHead normal.primitive := by
    obtain ⟨e,p,head,kind⟩ := normal.copyable.head_exists
    exact (MatchEmbedding.head_unique normal.head_at head).2 ▸ kind
  have terminal := CopyTrace.head_terminal
    (payload.matchEmbedding.primitive _ _ normal.head_at.1) kind
  generalize destination : payload.edges normal.head = finish at path
  induction path with
  | refl =>
    intro b m route
    cases route with
    | refl => exact initial
    | step hop tail => exact False.elim (terminal _ (destination ▸ hop))
  | @step a b c n hop tail ih =>
    obtain ⟨copy,_⟩ := (cert a.1).retained_of_not_hole initial
    have next (name) : C.edgeLabel b.1 ≠ primitiveLabel d (.hole name) := by
      intro hole
      obtain ⟨w,target,source⟩ := hop.2
      obtain ⟨v,eq⟩ := copy.target_origin target
      obtain ⟨i,input,attached⟩ := source_input_exact C (eq ▸ source)
      obtain ⟨k',h',W,copyable,free,related,owners⟩ :=
        payload_owner C cert closed hole i input normal payload (destination ▸ tail)
      exact last name ((congrArg C.edgeLabel (owners normal.head)).trans hole)
    intro e m route
    cases route with
    | refl => exact initial
    | step first rest =>
      have same := CopyTrace.hop_functional hop first
      subst same
      exact ih next destination rest

/-- The whole actual payload is retained once its primitive head is retained;
its possible lambda box follows a non-term input and preserves its full body. -/
theorem payload_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {k h}
    {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand L))
    (head : ∀ name, C.edgeLabel (payload.edges normal.head).1 ≠ primitiveLabel d (.hole name)) :
    ∀ e name, C.edgeLabel (payload.edges e).1 ≠ primitiveLabel d (.hole name) := by
  have different (e : V.Edge) :
      (C.expand L).edgeLabel (payload.edges e) ≠ primitiveLabel d (.contraction .term) := by
    intro label
    have original := (Search.primitive_equiv (payload.label e) (.contraction .term)).mpr label
    have allowed := copyable_primitive normal.copyable e (.contraction .term) original
    simp [PayloadPrimitive] at allowed
  intro e name
  rcases normal.edge_cases e with rfl | rfl
  · exact head name
  · cases normal with
    | plain d c => exact head name
    | lambda B =>
      obtain ⟨copy,_⟩ := (cert _).retained_of_not_hole head
      have adj : (lambdaPayload B).Adjacent (CopyRule.NormalForm.lambda B).head (CopyRule.NormalForm.lambda B).tail :=
        ⟨.internal (CopyRule.NormalForm.lambdaWire B),List.mem_cons_self,List.mem_cons_self⟩
      obtain ⟨w,target,source⟩ := payload.matchEmbedding.adjacent adj
      obtain ⟨v,eq⟩ := copy.target_origin target
      exact ForwardOverlap.source_not_hole C cert closed (eq ▸ source) (different _) name

end Hypernets.Copying.CopyingTemplate.Remote

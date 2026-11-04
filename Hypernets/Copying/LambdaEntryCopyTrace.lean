import Hypernets.Copying.CopyingTemplateFirstShallow
import Hypernets.Copying.ParametricityBoundaryBarrier

/-! First shallow entry of an actual copy trace for lambda-entry templates.
The prefix is an original context trace; the entered lambda is terminal for
copy tracing, and its whole recursive payload remains in that same hole. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryCopy
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)
include cert

/-- An actual copy trace either reflects entirely to the original context
or has its first shallow entry at one exact original ordered hole input. -/
theorem trace_cases {a b : (C.expand L).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand L)) a b n)
    (initial : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h)) :
    (Nonempty (Retained C L b.1) ∧ Trace (CopyTrace.Hop C) a.1 b.1 n) ∨
      CopyingTemplate.Remote.FirstShallow C L a b n := by
  induction path with
  | refl =>
    obtain ⟨copy,_⟩ := (cert _).retained_of_not_hole initial
    exact .inl ⟨⟨copy⟩,.refl _⟩
  | @step a b c n hop tail ih =>
    obtain ⟨copy,_⟩ := (cert a.1).retained_of_not_hole initial
    have original := BindingOverlap.copying_hop_owner C copy hop
    by_cases next : ∃ h, C.edgeLabel b.1 = primitiveLabel d (.hole h)
    · obtain ⟨name,label⟩ := next
      obtain ⟨w,target,source⟩ := hop.2
      obtain ⟨v,eq⟩ := copy.target_origin target
      obtain ⟨i,mem,attached⟩ := CopyingTemplate.Remote.source_input_exact C (eq ▸ source)
      have originalTarget : v ∈ C.target a.1 := target_owner C L (eq ▸ target)
      exact .inr ⟨b.1,name,i,b.2,a.1,0,n,label,mem,.refl _,original,
        attached ▸ originalTarget,tail,by omega⟩
    · have notHole : ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
        intro h eq; exact next ⟨h,eq⟩
      rcases ih notHole with ⟨last,rest⟩ | ⟨hole,name,i,entry,last,k,l,label,source,pre,hop,attached,suffix,total⟩
      · exact .inl ⟨last,.step original rest⟩
      · exact .inr ⟨hole,name,i,entry,last,k+1,l,label,source,.step original pre,hop,attached,suffix,by omega⟩

/-- A target of a shallow component with no outputs remains internal to that
component. An actual following edge therefore has exactly the same owner. -/
theorem shallow_adjacent_owner (none : T.NoOutputs) (closed : HoleFree (C.expand L))
    {a b : (C.expand L).Edge} {name : Hole}
    (hole : C.edgeLabel a.1 = primitiveLabel d (.hole name))
    (adj : (C.expand L).Adjacent a b) : b.1 = a.1 := by
  have empty := none ((cert a.1).relation_at_hole hole closed)
  obtain ⟨w,target,source⟩ := adj
  obtain ⟨x,tx,eqx⟩ := List.mem_map.mp target
  obtain ⟨y,sy,eqy⟩ := List.mem_map.mp source
  have eq := eqx.trans eqy.symm
  cases x with
  | input i => exact False.elim ((L a.1).target_not_input tx trivial)
  | output i => exact Fin.elim0 (Fin.cast (congrArg List.length empty) i)
  | internal x =>
    cases y with
    | input i =>
      exact False.elim (Net.Expansion.host_ne_internal C L (C.sourcePort b.1 i) a.1 x eq.symm)
    | output i => exact False.elim ((L b.1).source_not_output sy trivial)
    | internal y =>
      change (Port.internal (.inr ⟨a.1,x⟩) : (C.expand L).Vertex) = Port.internal (.inr ⟨b.1,y⟩) at eq
      exact (congrArg Sigma.fst (Sum.inr.inj (Port.internal.inj eq))).symm

/-- The first shallow entry is already the actual matched lambda head.
Its attached recursive box is in the same original hole, so every outer
payload edge has that owner and the complete lambda body stays intact. -/
theorem shallow_payload_owner (heads : T.LambdaEntries) (none : T.NoOutputs)
    (closed : HoleFree (C.expand L)) {hole : C.Edge} {name : Hole}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (L hole).Edge} (source : Port.input i ∈ (L hole).source entry)
    {k h} {V : Hypernet d [.term] (environmentInterface k h)}
    (normal : CopyRule.NormalForm V) (payload : Occurrence V (C.expand L)) {n}
    (suffix : Trace (CopyTrace.Hop (C.expand L)) ⟨hole,entry⟩ (payload.edges normal.head) n) :
    n = 0 ∧ normal.primitive = .operation .lam ∧
      (∀ e, (payload.edges e).1 = hole) := by
  have pair := (cert hole).relation_at_hole label closed
  obtain ⟨a,head⟩ := heads pair i
  have same := (L hole).source_unique source head.2
  have entryLabel : (C.expand L).edgeLabel ⟨hole,entry⟩ = primitiveLabel d (.operation .lam) := same ▸ head.1
  have terminal := CopyTrace.head_terminal entryLabel (by simp [CopyTrace.PayloadHead])
  have stop {x y : (C.expand L).Edge} {n} (path : Trace (CopyTrace.Hop (C.expand L)) x y n)
      (term : Terminal (CopyTrace.Hop (C.expand L)) x) : n = 0 ∧ y = x := by
    cases path with
    | refl => exact ⟨rfl,rfl⟩
    | step hop _ => exact False.elim (term _ hop)
  obtain ⟨count,sameHead⟩ := stop suffix terminal
  subst n
  have primitive : normal.primitive = .operation .lam := primitiveLabel_injective d
    ((payload.matchEmbedding.primitive _ _ normal.head_at.1).symm.trans ((congrArg (C.expand L).edgeLabel sameHead).trans entryLabel))
  refine ⟨rfl,primitive,?_⟩
  intro e
  rcases normal.edge_cases e with rfl | rfl
  · exact congrArg Sigma.fst sameHead
  · cases normal with
    | plain d c => exact congrArg Sigma.fst sameHead
    | lambda B =>
      have adj : (lambdaPayload B).Adjacent (CopyRule.NormalForm.lambda B).head (CopyRule.NormalForm.lambda B).tail :=
        ⟨.internal (CopyRule.NormalForm.lambdaWire B),List.mem_cons_self,List.mem_cons_self⟩
      exact (shallow_adjacent_owner C cert none closed
        ((congrArg C.edgeLabel (congrArg Sigma.fst sameHead)).trans label)
        (payload.matchEmbedding.adjacent adj)).trans (congrArg Sigma.fst sameHead)

end Hypernets.Copying.LambdaEntryCopy

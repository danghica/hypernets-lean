import Hypernets.Copying.CopyingTemplateForwardBarrier
import Hypernets.Copying.CopyPayloadRigidity

/-! Locate the first actual shallow copying component on a remote copy path.
The counted prefix is reflected in the original context, and the exact ordered
hole input is retained. No binding-free restriction or path choice is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.Remote
open Graph Opening Search.Expansion

/-- A source incidence at an original vertex records the actual component
input and its exact original attachment, not merely the existence of an input. -/
theorem source_input_exact {d I O} (C : Hypernet d I O) {F}
    {e : (C.expand F).Edge} {v : C.Vertex}
    (source : Net.Expansion.host C F v ∈ (C.expand F).source e) :
    ∃ i, Port.input i ∈ (F e.1).source e.2 ∧ C.sourcePort e.1 i = v := by
  obtain ⟨w,mem,eq⟩ := List.mem_map.mp source
  cases w with
  | internal a => exact False.elim (Net.Expansion.host_ne_internal C F v e.1 a eq.symm)
  | input i => exact ⟨i,mem,Net.Expansion.host_injective C F eq⟩
  | output i => exact False.elim ((F e.1).source_not_output mem trivial)

/-- The first shallow entry splits the actual counted copy path into an
original-context prefix and the remaining original expanded-graph suffix. -/
def FirstShallow {d I O} (C : Hypernet d I O) (F)
    (a b : (C.expand F).Edge) (n : Nat) : Prop :=
  ∃ (hole : C.Edge) (name : Hole)
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    (entry : (F hole).Edge) (last : C.Edge) (k l : Nat),
    C.edgeLabel hole = primitiveLabel d (.hole name) ∧
    Port.input i ∈ (F hole).source entry ∧
    Trace (CopyTrace.Hop C) a.1 last k ∧
    CopyTrace.Hop C last hole ∧ C.sourcePort hole i ∈ C.target last ∧
    Trace (CopyTrace.Hop (C.expand F)) ⟨hole,entry⟩ b l ∧
    n = k+1+l

/-- A remote sharing trace either stays wholly in the original context or
has a first shallow entry with a positive retained prefix and exact input. -/
theorem trace_cases {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    {a b : (C.expand L).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand L)) a b n)
    (initial : ∀ h, C.edgeLabel a.1 ≠ primitiveLabel d (.hole h)) :
    (Nonempty (Retained C L b.1) ∧ Trace (CopyTrace.Hop C) a.1 b.1 n) ∨
      FirstShallow C L a b n := by
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
      obtain ⟨i,mem,attached⟩ := source_input_exact C (eq ▸ source)
      have originalTarget : v ∈ C.target a.1 := target_owner C L (eq ▸ target)
      exact .inr ⟨b.1,name,i,b.2,a.1,0,n,label,mem,.refl _,original,
        attached ▸ originalTarget,tail,by omega⟩
    · have notHole : ∀ h, C.edgeLabel b.1 ≠ primitiveLabel d (.hole h) := by
        intro h eq; exact next ⟨h,eq⟩
      rcases ih notHole with ⟨last,rest⟩ | ⟨hole,name,i,entry,last,k,l,label,source,pre,hop,attached,suffix,total⟩
      · exact .inl ⟨last,.step original rest⟩
      · exact .inr ⟨hole,name,i,entry,last,k+1,l,label,source,.step original pre,hop,attached,suffix,by omega⟩

/-- At that first original hole input the actual copying-source edge is a
term contraction. This is the unique possible shallow forward overlap. -/
theorem first_entry_contraction {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {hole : C.Edge} {name}
    (label : C.edgeLabel hole = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel hole)).length)
    {entry : (L hole).Edge} (source : Port.input i ∈ (L hole).source entry) :
    (L hole).edgeLabel entry = primitiveLabel d (.contraction .term) := by
  have pair := (cert hole).relation_at_hole label closed
  obtain ⟨e,head⟩ := pair.left_input_head i
  exact (L hole).source_unique source head.2 ▸ head.1

end Hypernets.Copying.CopyingTemplate.Remote

import Hypernets.Copying.CopyingTemplate
import Hypernets.Copying.CopyPayloadNormal
import Hypernets.Copying.BindingCopyOverlap

/-! Only term-sharing, ordinary operation, and instance primitives occur on
the outer surface of a copying source. Arbitrary recursive lambda bodies are
left unrestricted. In particular, no atom tree or store is hidden shallowly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate
open Graph Search.Expansion

/-- The exact primitive possibilities at the surface of a copyable payload. -/
def PayloadPrimitive (p : Primitive) : Prop :=
  p = .instanceEdge ∨ ∃ o, p = .operation o

/-- A primitive edge of an original copyable payload is an instance or an
operation. Its possible box body is intentionally outside this assertion. -/
theorem copyable_primitive {d k h} {H : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable H) (e : H.Edge) (p : Primitive)
    (label : H.edgeLabel e = primitiveLabel d p) : PayloadPrimitive p := by
  obtain ⟨K,⟨normal⟩,⟨f⟩⟩ := CopyRule.normal_form copyable
  have mapped := (MatchEmbedding.ofDeepIso f).primitive e p label
  cases normal with
  | plain d c =>
    cases d <;> cases c
    all_goals
      first
      | have eq := congrArg ULift.down mapped
        simp only [CopyRule.PlainCode.net,primitiveNet,primitiveLabel] at eq
        subst p
        simp [PayloadPrimitive]
      | have eq := Sum.inl.inj mapped
        subst p
        simp [PayloadPrimitive]
  | lambda B =>
    change (lambdaPayload B).edgeLabel (f.edges.toFun e) = _ at mapped
    generalize f.edges.toFun e = edge at mapped
    obtain ⟨b,a⟩ := edge
    cases b with
    | false =>
      have eq : .operation .lam = p := Sum.inl.inj mapped
      subst p
      exact .inr ⟨_,rfl⟩
    | true => cases mapped

/-- The whole source adds only term weakening/contraction to the original
copyable payload's outer primitive labels. -/
theorem Literal.left_primitive_cases {d I O} {G H : Hypernet d I O}
    (pair : Literal G H) (e : G.Edge) (p : Primitive)
    (label : G.edgeLabel e = primitiveLabel d p) :
    p = .weakening .term ∨ p = .contraction .term ∨ PayloadPrimitive p := by
  cases pair with
  | copy tree A copyable free =>
    obtain ⟨part,e⟩ := e
    cases part with
    | false =>
      cases d with
      | zero =>
        have eq : tree.net.edgeLabel e = p := congrArg ULift.down label
        rcases tree.labels e with weak | contr
        · exact .inl (eq.symm.trans weak)
        · exact .inr (.inl (eq.symm.trans contr))
      | succ d =>
        have eq : tree.net.edgeLabel e = p := Sum.inl.inj label
        rcases tree.labels e with weak | contr
        · exact .inl (eq.symm.trans weak)
        · exact .inr (.inl (eq.symm.trans contr))
    | true =>
      cases d <;> exact .inr (.inr (copyable_primitive copyable e p label))

/-- Full recursive graph isomorphism preserves this outer-surface restriction. -/
theorem Pair.left_primitive_cases {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) (e : G.Edge) (p : Primitive)
    (label : G.edgeLabel e = primitiveLabel d p) :
    p = .weakening .term ∨ p = .contraction .term ∨ PayloadPrimitive p := by
  cases pair with
  | witness f literal g =>
    exact literal.left_primitive_cases (f.edges.toFun e) p
      ((MatchEmbedding.ofDeepIso f).primitive e p label)

namespace ForwardOverlap
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
include cert

/-- Any primitive excluded from the source's outer surface has an original
non-hole owner. The retained-hole possibility is excluded by its exact label. -/
theorem forbidden_primitive_not_hole {e : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (weak : p ≠ .weakening .term) (contr : p ≠ .contraction .term)
    (payload : ¬ PayloadPrimitive p) (notHole : ∀ h, p ≠ .hole h) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro hole
  rcases (cert e.1).origin with copies | ⟨name,_,pair⟩
  · obtain ⟨copy⟩ := copies.1
    have original : C.edgeLabel e.1 = primitiveLabel d p := by
      apply (copy.primitive p).mp
      change (L e.1).edgeLabel e.2 = _ at label
      simpa only [copy.only e.2] using label
    exact notHole h (primitiveLabel_injective d (original.symm.trans hole))
  · rcases pair.left_primitive_cases e.2 p label with impossible | impossible | impossible
    · exact weak impossible
    · exact contr impossible
    · exact payload impossible

/-- Every actual atom-sharing branch is retained, including unused siblings. -/
theorem atom_sharing_not_hole {e : (C.expand L).Edge}
    (label : (C.expand L).edgeLabel e = primitiveLabel d (.weakening .atom) ∨
      (C.expand L).edgeLabel e = primitiveLabel d (.contraction .atom)) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  rcases label with label | label
  all_goals
    exact forbidden_primitive_not_hole C cert label
      (by intro eq; cases eq) (by intro eq; cases eq)
      (by simp [PayloadPrimitive]) (by intro h eq; cases eq) h

/-- The actual store cannot be supplied by a shallow copying component. -/
theorem store_not_hole {e : (C.expand L).Edge}
    (label : (C.expand L).edgeLabel e = primitiveLabel d .store) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) :=
  forbidden_primitive_not_hole C cert label
    (by intro eq; cases eq) (by intro eq; cases eq)
    (by simp [PayloadPrimitive]) (by intro h eq; cases eq) h

end ForwardOverlap
end Hypernets.Copying.CopyingTemplate

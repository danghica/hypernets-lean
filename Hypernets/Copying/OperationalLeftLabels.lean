import Hypernets.Copying.OperationalTemplateLaws
import Hypernets.Copying.BindingCopyOverlap
import Hypernets.Copying.RetainedFootprint

/-! The original operational templates have restricted outer labels on their
left sides. Nested lambda bodies remain arbitrary; no restriction is imposed
on their contents. These facts exclude entire original sharing-tree footprints
from shallow operational holes, including unused sibling branches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates
open Graph

/-- The active head of the original left operational graph. -/
def Kind.head : Kind → Operation
  | .microBeta => .app
  | .referenceCreation => .unary .ref

/-- Reading a primitive label of a flat stable graph retains the paper's
passivity or instance restriction. -/
theorem stable_primitive {d O} {G : Hypernet d [.term] O} (stable : Stable G)
    (e : G.Edge) (p : Primitive) (label : G.edgeLabel e = primitiveLabel d p) :
    StablePrimitive p := by
  obtain ⟨q,eq,allowed⟩ := stable.labels e
  have same := primitiveLabel_injective d (eq.symm.trans label)
  subst q
  exact allowed

/-- Every primitive outer edge is the active head or a stable argument edge.
The lambda box is excluded only from this primitive classification; its
actual body can contain arbitrary operations, sharing and nested boxes. -/
theorem Literal.left_primitive_cases {kind d I O} {G H : Hypernet d I O}
    (pair : Literal kind G H) (e : G.Edge) (p : Primitive)
    (label : G.edgeLabel e = primitiveLabel d p) :
    p = .operation kind.head ∨ StablePrimitive p := by
  cases pair with
  | beta B G free stable =>
    obtain ⟨part,e⟩ := e
    cases part with
    | false =>
      left
      exact (Sum.inl.inj label).symm
    | true =>
      obtain ⟨part,e⟩ := e
      cases part with
      | true => exact .inr (stable_primitive stable e p label)
      | false =>
        obtain ⟨part,e⟩ := e
        cases part with
        | false =>
          have same : .operation .lam = p := Sum.inl.inj label
          subst p
          exact .inr rfl
        | true => cases label
  | reference G stable =>
    obtain ⟨part,e⟩ := e
    cases part with
    | false =>
      left
      cases d with
      | zero => exact (congrArg ULift.down label).symm
      | succ d => exact (Sum.inl.inj label).symm
    | true =>
      right
      cases d <;> exact stable_primitive stable e p label

/-- Independent endpoint representation changes preserve the outer restriction. -/
theorem Pair.left_primitive_cases {kind d I O} {G H : Hypernet d I O}
    (pair : Pair kind G H) (e : G.Edge) (p : Primitive)
    (label : G.edgeLabel e = primitiveLabel d p) :
    p = .operation kind.head ∨ StablePrimitive p := by
  cases pair with
  | witness f pair g =>
    exact pair.left_primitive_cases (f.edges.toFun e) p ((MatchEmbedding.ofDeepIso f).primitive e p label)

/-- No outer weakening edge can occur in the original left template graph. -/
theorem Pair.left_not_weakening {kind d I O} {G H : Hypernet d I O}
    (pair : Pair kind G H) (e : G.Edge) (s : ShareSort) :
    G.edgeLabel e ≠ primitiveLabel d (.weakening s) := by
  intro label
  rcases pair.left_primitive_cases e _ label with impossible | impossible
  · cases impossible
  · exact impossible

/-- No outer contraction edge can occur in the original left template graph. -/
theorem Pair.left_not_contraction {kind d I O} {G H : Hypernet d I O}
    (pair : Pair kind G H) (e : G.Edge) (s : ShareSort) :
    G.edgeLabel e ≠ primitiveLabel d (.contraction s) := by
  intro label
  rcases pair.left_primitive_cases e _ label with impossible | impossible
  · cases impossible
  · exact impossible

end Hypernets.Copying.OperationalTemplates

namespace Hypernets.Copying.BindingOverlap
open Graph Search.Expansion OperationalTemplates
variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
include cert

/-- A forbidden primitive cannot be supplied by a shallow operational hole.
The retained-hole case is also excluded explicitly; no closure assumption is
needed for unrelated parts of the original expansion. -/
theorem forbidden_primitive_not_hole {e : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (active : p ≠ .operation kind.head) (stable : ¬ StablePrimitive p)
    (notHole : ∀ h, p ≠ .hole h) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  intro hole
  rcases (cert e.1).origin with copies | ⟨name,_,pair⟩
  · obtain ⟨copy⟩ := copies.1
    have original : C.edgeLabel e.1 = primitiveLabel d p := by
      apply (copy.primitive p).mp
      change (L e.1).edgeLabel e.2 = _ at label
      simpa only [copy.only e.2] using label
    exact notHole h (primitiveLabel_injective d (original.symm.trans hole))
  · rcases pair.left_primitive_cases e.2 p label with forbidden | forbidden
    · exact active forbidden
    · exact stable forbidden

/-- Every original term or atom sharing edge avoids shallow left operational
contributions, including sharing edges off the active copying spine. -/
theorem sharing_not_hole {e : (C.expand L).Edge} (s : ShareSort)
    (label : (C.expand L).edgeLabel e = primitiveLabel d (.weakening s) ∨
      (C.expand L).edgeLabel e = primitiveLabel d (.contraction s)) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) := by
  rcases label with label | label
  all_goals
    exact forbidden_primitive_not_hole C cert label
      (by intro eq; cases eq) (by exact id) (by intro h eq; cases eq) h

/-- Store edges are absent from both original left operational families. -/
theorem store_not_hole {e : (C.expand L).Edge}
    (label : (C.expand L).edgeLabel e = primitiveLabel d .store) (h : Hole) :
    C.edgeLabel e.1 ≠ primitiveLabel d (.hole h) :=
  forbidden_primitive_not_hole C cert label
    (by intro eq; cases eq) (by exact id) (by intro h eq; cases eq) h

end Hypernets.Copying.BindingOverlap

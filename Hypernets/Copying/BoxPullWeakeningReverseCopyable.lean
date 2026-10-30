import Hypernets.Copying.BoxPullWeakeningReverseLambda

/-! Actual copyable payloads remain enabled in the converse direction. The
lambda case retains the original larger box environment; no altered rule or
translation is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Opening
namespace ReverseComponents

theorem primitive_nonweak (d : Nat) (p : Primitive) (notweak : ∀ s, p ≠ .weakening s) :
    ∀ e : (primitiveNet d p).Edge, ∃ q,
      (primitiveNet d p).edgeLabel e = primitiveLabel d q ∧ ∀ s, q ≠ .weakening s := by
  intro e
  let c := Occurrence.primitiveCopy d p
  exact ⟨p,(congrArg (primitiveNet d p).edgeLabel (c.only e)).trans c.edge_label,notweak⟩

theorem stable_nonweak {d J} {A : Hypernet d [.term] J} (stable : Stable A) :
    ∀ e, ∃ p, A.edgeLabel e = primitiveLabel d p ∧ ∀ s, p ≠ .weakening s := by
  intro e
  obtain ⟨p,label,passive⟩ := stable.labels e
  exact ⟨p,label,fun s eq => by subst p; exact passive⟩
end ReverseComponents

namespace Decoration
/-- Reflection may enlarge a lambda's free interface, while preserving its
single actual incoming term port. All Copyable constructors are covered. -/
theorem reflectCopyable {d k h} {A : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable A) :
    ∀ {I O} {G : Hypernet d I O} (D : Decoration G) (f : Occurrence A D.graph),
    ∃ k' h', ∃ B : Hypernet d [.term] (environmentInterface k' h'), Copyable B ∧
      ∃ g : Occurrence B G, ∀ i, g.ports (.input i) = D.project (f.ports (.input i)) := by
  induction copyable with
  | instanceEdge d =>
    intro I O G D f
    exact ⟨0,1,_,.instanceEdge d,D.reflectPrimitiveOccurrence f.matchEmbedding
      (ReverseComponents.primitive_nonweak d .instanceEdge (fun s eq => by cases eq)),fun _ => rfl⟩
  | constant d c =>
    intro I O G D f
    exact ⟨0,0,_,.constant d c,D.reflectPrimitiveOccurrence f.matchEmbedding
      (ReverseComponents.primitive_nonweak d (.operation (.const c)) (fun s eq => by cases eq)),fun _ => rfl⟩
  | application d =>
    intro I O G D f
    exact ⟨2,0,_,.application d,D.reflectPrimitiveOccurrence f.matchEmbedding
      (ReverseComponents.primitive_nonweak d (.operation .app) (fun s eq => by cases eq)),fun _ => rfl⟩
  | unary d o =>
    intro I O G D f
    exact ⟨1,0,_,.unary d o,D.reflectPrimitiveOccurrence f.matchEmbedding
      (ReverseComponents.primitive_nonweak d (.operation (.unary o)) (fun s eq => by cases eq)),fun _ => rfl⟩
  | binary d o =>
    intro I O G D f
    exact ⟨2,0,_,.binary d o,D.reflectPrimitiveOccurrence f.matchEmbedding
      (ReverseComponents.primitive_nonweak d (.operation (.binary o)) (fun s eq => by cases eq)),fun _ => rfl⟩
  | lambda body =>
    intro I O G D f
    obtain ⟨k,h,B,g,inputs⟩ := D.reflectLambda body f
    exact ⟨k,h,lambdaPayload B,.lambda B,g,inputs⟩
  | rename iso copyable ih =>
    intro I O G D f
    exact ih D ((Occurrence.ofIso iso).comp f)
end Decoration
end Hypernets.Copying.BoxPullWeakening

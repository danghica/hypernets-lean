import Hypernets.Copying.CopyTransport

/-! Ordered residual wiring, literal box copying, and repeated reference use. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

def residualTreeVertex {n} (T : ContractionTree .term (n+1)) (d : Nat) (v : T.net.Vertex) :
    (residual T d).Vertex := Net.Expansion.insert (residualFrame n) (residualFill T) true v

/-- The selected input is replaced by an actual weakening output. -/
theorem selected_input_weakened {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    (residual T d).target (residualWeakening T d) =
      [residualTreeVertex T d (.input ⟨0,by simp⟩)] := rfl

/-- All remaining tree inputs stay external, in their original order. -/
theorem residual_input_order {n} (T : ContractionTree .term (n+1)) (d : Nat) (i : Fin n) :
    residualTreeVertex T d (.input ⟨i.val+1,by simp⟩) =
      .input ⟨i.val,by simp⟩ := by
  simp [residualTreeVertex,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,
    residualFrame,residualSource,Port.map]

/-- The tree's entire ordered source incidence survives the rule. -/
theorem residual_sources {n} (T : ContractionTree .term (n+1)) (d : Nat) (e : T.net.Edge) :
    (residual T d).source (residualTreeEdge T d e) = (T.net.source e).map (residualTreeVertex T d) := rfl

theorem residual_targets {n} (T : ContractionTree .term (n+1)) (d : Nat) (e : T.net.Edge) :
    (residual T d).target (residualTreeEdge T d e) = (T.net.target e).map (residualTreeVertex T d) := rfl

/-- The unrestricted literal lambda payload satisfies the rule's side condition. -/
theorem lambda_rule {d n k h} (T : ContractionTree .term (n+1))
    (body : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Rule (before T (lambdaPayload body)) (after T (lambdaPayload body)) :=
  .copy T _ (.lambda body)

/-- Every box label is duplicated unchanged, including its complete nested contents. -/
theorem lambda_box_preserved {d n k h} (T : ContractionTree .term (n+1))
    (body : Hypernet d [.term] (environmentInterface (k+1) h))
    (e : (lambdaPayload body).Edge) (b : Box (alphabet d))
    (label : (lambdaPayload body).edgeLabel e = .inr b) :
    (after T (lambdaPayload body)).edgeLabel (leftEdge T _ e) = .inr b ∧
    (after T (lambdaPayload body)).edgeLabel (rightEdge T _ e) = .inr b := by
  exact ⟨(copy_labels T _ e).1.trans label,(copy_labels T _ e).2.trans label⟩

/-- Copying active operations is permitted too; a passive-only restriction is incorrect. -/
theorem application_rule {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    Rule (before (k := 2) (h := 0) T (primitiveNet d (.operation .app)))
      (after T (primitiveNet d (.operation .app))) := .copy T _ (.application d)

/-- The consumed tree is not replaced by a canonical tree: even a weakening-free
binary presentation remains the matched tree on the residual side. -/
theorem binary_residual_weakening (d : Nat) :
    (residual (Examples.binaryTree .term) d).edgeLabel
      (residualWeakening (Examples.binaryTree .term) d) = primitiveLabel d (.weakening .term) := rfl

/-- Two distinct copies of a reference resolve to one cell, not two fresh cells. -/
theorem binary_shared_reference :
    sharedLeft (Examples.binaryTree .term) ≠ sharedRight (Examples.binaryTree .term) ∧
    StoreTrace.Resolves (sharedStore (Examples.binaryTree .term))
      (sharedLeft (Examples.binaryTree .term)) (sharedCell (Examples.binaryTree .term)) 3 ∧
    StoreTrace.Resolves (sharedStore (Examples.binaryTree .term))
      (sharedRight (Examples.binaryTree .term)) (sharedCell (Examples.binaryTree .term)) 3 := by
  refine ⟨?_,shared_resolves _⟩
  intro eq
  exact copies_disjoint (k := 0) (h := 1) (Examples.binaryTree .term) (primitiveNet 0 .instanceEdge) (0 : Fin 1) (0 : Fin 1)
    (eq_of_heq (Sigma.mk.inj eq).2)
end Hypernets.Copying.CopyRule

import Hypernets.Copying.CopyBoundaryNaturality

/-! The shallow BPerm/copying overlap for arbitrary lambda bodies and genuine
contraction trees. Both surviving boxes are accounted for; no semantic BPerm law
is assumed in constructing the residual structural derivation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace BoxPermutation.Derivation

/-- Equality casts and literal boundary reindexing express the same closure. -/
theorem reboundary {d I O J K} {G H : Hypernet d I O} (s : Derivation G H)
    (hi : I = J) (ho : O = K) : Derivation (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho; simpa only [Net.reboundary_refl] using s

/-- Copying duplicates a structural derivation in the two disjoint branches.
This is a closure lemma, not a claim that arbitrary derivations are sound. -/
theorem copies {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (s : Derivation G H) (T : ContractionTree .term (n+1)) :
    Derivation (CopyRule.copies T G) (CopyRule.copies T H) := by
  apply Derivation.reboundary
  apply Derivation.parallel
  intro b; cases b
  · exact s
  · exact (refl _).serial s

theorem copyingAfter {d n k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (s : Derivation G H) (T : ContractionTree .term (n+1)) :
    Derivation (CopyRule.after T G) (CopyRule.after T H) := (s.copies T).serial (refl _)
end BoxPermutation.Derivation

namespace BoxPermutation.Copying
variable {d n k h : Nat} (T : ContractionTree .term (n+1))
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))

/-- The compensation is at the free outputs of the original box. -/
def compensatedPayload (C : Hypernet d [.term] (environmentInterface (k+1) h))
    (p : TypedPermutation (environmentInterface k h)) :
    Hypernet (d+1) [.term] (environmentInterface k h) :=
  Serial.net (primitiveNet (d+1) (.operation .lam))
    (InterfacePermutation.net (Translation.lambdaBox C) p.symm)

def payloadIso : DeepIso (compensatedPayload C p) (InterfacePermutation.net (lambdaPayload C) p.symm) :=
  InterfacePermutation.serial _ (Translation.lambdaBox C) p.symm

theorem payload_pair (action : Opening.Action f p) :
    Derivation (lambdaPayload B) (compensatedPayload C p) :=
  (Derivation.refl _).serial (Derivation.of_upToIso (Opening.lambda_pair f p action))

theorem source_pair (action : Opening.Action f p) :
    Derivation (CopyRule.before T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.before T (lambdaPayload C)) p.symm) :=
  ((Derivation.refl _).serial ((payload_pair f p action).trans (.iso (payloadIso p)))).trans
    (.iso (InterfacePermutation.serial _ (lambdaPayload C) p.symm))

/-- The two residual pairs are assembled using the unchanged residual tree and
both distributors; the boundary naturality law moves the compensation outside. -/
theorem residual_pair (action : Opening.Action f p) :
    Derivation (CopyRule.after T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.after T (lambdaPayload C)) p.symm) :=
  ((payload_pair f p action).copyingAfter T).trans
    (.iso ((CopyRule.after_congr (Net.Iso.refl _) (payloadIso p)).trans
      (CopyRule.Boundary.permuted T p.symm)))

/-- Exactly one genuine copying transition on each side, with both copyability
premises proved from the lambda shape. External compensation uses context closure. -/
theorem copy_diamond (action : Opening.Action f p) :
    Combined.Step ⟨CopyRule.before T (lambdaPayload B),(.rewrite,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩ ∧
    Combined.Step (InterfacePermutation.state p.symm
        ⟨CopyRule.before T (lambdaPayload C),(.rewrite,.input ⟨0,by simp⟩)⟩)
      (InterfacePermutation.state p.symm
        ⟨CopyRule.after T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩) ∧
    Derivation (CopyRule.after T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.after T (lambdaPayload C)) p.symm) :=
  ⟨Combined.local_step (.copy T _ (.lambda B)),
    InterfacePermutation.step _ (Combined.local_step (.copy T _ (.lambda C))),
    residual_pair T f p action⟩

/-- Search and copying cost two transitions on both sides, without any condition
on the body, its termination, the number of residual inputs, or tree presentation. -/
theorem initial_diamond (action : Opening.Action f p) :
    (Combined.machine (d+1) (List.replicate (n+1) .term) (environmentInterface k h)).Steps 2
      ⟨CopyRule.before T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩
      ⟨CopyRule.after T (lambdaPayload B),(.search,.input ⟨0,by simp⟩)⟩ ∧
    (Combined.machine (d+1) (List.replicate (n+1) .term) (environmentInterface k h)).Steps 2
      (InterfacePermutation.state p.symm
        ⟨CopyRule.before T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩)
      (InterfacePermutation.state p.symm
        ⟨CopyRule.after T (lambdaPayload C),(.search,.input ⟨0,by simp⟩)⟩) ∧
    Derivation (CopyRule.after T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.after T (lambdaPayload C)) p.symm) :=
  ⟨.cons (.search _ (CopyRule.requests_copy T _)) (.cons (copy_diamond T f p action).1 (.zero _)),
    InterfacePermutation.run _ (.cons (.search _ (CopyRule.requests_copy T _))
      (.cons (Combined.local_step (.copy T _ (.lambda C))) (.zero _))),
    residual_pair T f p action⟩

/-- The actual box edge of the unmodified lambda payload. -/
def boxEdge (B : Hypernet d [.term] (environmentInterface (k+1) h)) : (lambdaPayload B).Edge :=
  Serial.rightEdge _ _ (0 : Fin 1)

/-- Literal box bodies survive in both copies, rather than being replaced with
boundary data or a predicate about their behaviour. -/
theorem residual_box_labels (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    (CopyRule.after T (lambdaPayload B)).edgeLabel (CopyRule.leftEdge T _ (boxEdge B)) =
      (Translation.lambdaBox B).edgeLabel (0 : Fin 1) ∧
    (CopyRule.after T (lambdaPayload B)).edgeLabel (CopyRule.rightEdge T _ (boxEdge B)) =
      (Translation.lambdaBox B).edgeLabel (0 : Fin 1) := CopyRule.copy_labels T _ (boxEdge B)

theorem residual_boxes_distinct (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    CopyRule.leftEdge T (lambdaPayload B) (boxEdge B) ≠ CopyRule.rightEdge T _ (boxEdge B) :=
  CopyRule.copies_disjoint T _ _ _

/-- Instantiating the body action needs no unproved robustness or translation premise. -/
theorem permuted_copying (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (p : TypedPermutation (environmentInterface k h)) :
    Derivation (CopyRule.before T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.before T
        (lambdaPayload (InterfacePermutation.net B (Opening.bodyPermutation p)))) p.symm) ∧
    Derivation (CopyRule.after T (lambdaPayload B))
      (InterfacePermutation.net (CopyRule.after T
        (lambdaPayload (InterfacePermutation.net B (Opening.bodyPermutation p)))) p.symm) :=
  ⟨source_pair T _ p (Opening.permuted_action B p),residual_pair T _ p (Opening.permuted_action B p)⟩
end BoxPermutation.Copying
end Hypernets.Copying

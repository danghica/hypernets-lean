import Hypernets.Copying.CopyPayloadNormal

/-! Independent copyable matches of one actual payload agree on its full recursive graph. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph

def comp {d I O J K L M} {A : Hypernet d I O} {B : Hypernet d J K} {C : Hypernet d L M}
    (f : Occurrence A B) (g : Occurrence B C) : Occurrence A C where
  ports := g.ports ∘ f.ports
  internals := g.internals ∘ f.internals
  edges := g.edges ∘ f.edges
  internal_map x := by simp only [Function.comp_apply,f.internal_map,g.internal_map]
  internal_injective := g.internal_injective.comp f.internal_injective
  edge_injective := g.edge_injective.comp f.edge_injective
  internal_label x := (g.internal_label _).trans (f.internal_label x)
  label e := labelEquiv_trans _ (f.label e) (g.label _)
  source e := by rw [← List.map_map,f.source,g.source]; rfl
  target e := by rw [← List.map_map,f.target,g.target]; rfl

def serialRight {d I J K} (A : Hypernet d I J) (B : Hypernet d J K) : Occurrence B (Serial.net A B) where
  ports := BoundarySerial.rightInsert A B
  internals x := by cases d <;> exact .inr ⟨true,x⟩
  edges e := Serial.rightEdge A B e
  internal_map x := by cases d <;> rfl
  internal_injective := by cases d <;> exact fun _ _ h => eq_of_heq (Sigma.mk.inj (Sum.inr.inj h)).2
  edge_injective := by cases d <;> exact fun _ _ h => eq_of_heq (Sigma.mk.inj h).2
  internal_label x := by cases d <;> rfl
  label e := by cases d <;> exact labelEquiv_refl _ _
  source e := by cases d <;> rfl
  target e := by cases d <;> rfl
end Hypernets.Copying.Opening.Occurrence

namespace Hypernets.Copying.CopyRule
open Graph Opening

/-- The interface metadata agree and the entire payloads are recursively isomorphic. -/
inductive PayloadRelated : {d k h l j : Nat} → Hypernet d [.term] (environmentInterface k h) →
    Hypernet d [.term] (environmentInterface l j) → Prop where
  | graphs {d k h} {A B : Hypernet d [.term] (environmentInterface k h)} (iso : DeepIso A B) : PayloadRelated A B

namespace NormalForm

def lambdaWire {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) : (lambdaPayload B).Internal :=
  .inl (0 : Fin 1)
theorem lambda_head_target {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    (lambdaPayload B).target (NormalForm.lambda B).head = [.internal (lambdaWire B)] := rfl
theorem lambda_tail_source {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    (lambdaPayload B).source (NormalForm.lambda B).tail = [.internal (lambdaWire B)] := rfl

theorem related {d k h l j I O} {A : Hypernet d [.term] (environmentInterface k h)}
    {B : Hypernet d [.term] (environmentInterface l j)} {G : Hypernet d I O}
    (a : NormalForm A) (b : NormalForm B) (f : Occurrence A G) (g : Occurrence B G)
    (same : f.edges a.head = g.edges b.head) : PayloadRelated A B ∧ f.edges a.tail = g.edges b.tail := by
  have prim : a.primitive = b.primitive := primitiveLabel_injective d
    ((f.matchEmbedding.primitive _ _ a.head_at.1).symm.trans
      ((congrArg G.edgeLabel same).trans (g.matchEmbedding.primitive _ _ b.head_at.1)))
  cases a with
  | plain d c => cases b with
    | plain d c' =>
      have eq := PlainCode.primitive_injective prim
      subst c'
      exact ⟨.graphs (DeepIso.refl _),same⟩
    | lambda body => exact False.elim (c.not_lambda prim)
  | lambda body => cases b with
    | plain d c => exact False.elim (c.not_lambda prim.symm)
    | lambda body' =>
      have targets := (f.target (NormalForm.lambda body).head).trans
        ((congrArg G.target same).trans (g.target (NormalForm.lambda body').head).symm)
      rw [lambda_head_target,lambda_head_target] at targets
      simp only [List.map_cons,List.map_nil,f.internal_map,g.internal_map,List.cons.injEq] at targets
      have wires := targets.1
      have tailEq : f.edges (NormalForm.lambda body).tail = g.edges (NormalForm.lambda body').tail :=
        G.source_unique
          (by rw [← f.source,lambda_tail_source]; exact List.mem_cons_self)
          (by rw [← g.source,lambda_tail_source]; simpa only [List.map_cons,List.map_nil,g.internal_map,f.internal_map,← wires] using
            (List.mem_cons_self : f.ports (.internal (lambdaWire body)) ∈ [f.ports (.internal (lambdaWire body))]))
      have rel := labelEquiv_trans _ (f.label (NormalForm.lambda body).tail)
        (labelEquiv_symm _ (tailEq ▸ g.label (NormalForm.lambda body').tail))
      change BoxRelated _ (fun X Y => Nonempty (DeepIso X Y))
        ⟨1,_,_,Translation.castInterfaces rfl (by rw [Nat.add_comm _ 1]) body⟩
        ⟨1,_,_,Translation.castInterfaces rfl (by rw [Nat.add_comm _ 1]) body'⟩ at rel
      cases rel with
      | bodies iso =>
        obtain ⟨iso⟩ := iso
        exact ⟨.graphs (Serial.congr (DeepIso.refl _) (box_congr iso)),tailEq⟩
end NormalForm
end Hypernets.Copying.CopyRule

import Hypernets.Copying.TranslationClauses

/-! Definition 10.2 for O^ex. Only lambda has a thunk output, so its box
forest contains exactly one box; other operations have no box outputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- A lambda head and its box, before the translation adds environment distributors. -/
def lambdaPayload {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.term] (environmentInterface k h) :=
  Serial.net (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox G)

/-- The exact instance/operation-with-boxes shapes of Definition 10.2 for O^ex,
closed under recursive graph renaming. Box bodies are not required to be stable. -/
inductive Copyable : {d k h : Nat} → Hypernet d [.term] (environmentInterface k h) → Prop where
  | instanceEdge (d : Nat) : Copyable (d := d) (k := 0) (h := 1) (primitiveNet d .instanceEdge)
  | constant (d : Nat) (c : Constant) : Copyable (d := d) (k := 0) (h := 0) (primitiveNet d (.operation (.const c)))
  | application (d : Nat) : Copyable (d := d) (k := 2) (h := 0) (primitiveNet d (.operation .app))
  | unary (d : Nat) (o : Unary) : Copyable (d := d) (k := 1) (h := 0) (primitiveNet d (.operation (.unary o)))
  | binary (d : Nat) (o : Binary) : Copyable (d := d) (k := 2) (h := 0) (primitiveNet d (.operation (.binary o)))
  | lambda {d k h} (body : Hypernet d [.term] (environmentInterface (k+1) h)) : Copyable (lambdaPayload body)
  | rename {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
      (iso : DeepIso G H) : Copyable G → Copyable H

namespace Copyable

/-- Only instance, operation, and box labels can occur on the outer level. -/
def OuterLabel : (d : Nat) → (alphabet d).Symbol → Prop
  | 0, .up (.instanceEdge) => True
  | 0, .up (.operation _) => True
  | _+1, .inl .instanceEdge => True
  | _+1, .inl (.operation _) => True
  | _+1, .inr _ => True
  | _, _ => False

theorem outer_equiv (d : Nat) {a b : (alphabet d).Symbol} (h : LabelEquiv d a b) :
    OuterLabel d a ↔ OuterLabel d b := by
  cases d with
  | zero => change a = b at h; cases h; rfl
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => change a = b at h; cases h; rfl
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b => rfl

/-- Copyable payloads contain no outer contraction, weakening, store, focus, or hole. -/
theorem outer_labels {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (h : Copyable G) : ∀ e, OuterLabel d (G.edgeLabel e) := by
  induction h with
  | instanceEdge d => intro e; cases d <;> trivial
  | constant d c => intro e; cases d <;> trivial
  | application d => intro e; cases d <;> trivial
  | unary d o => intro e; cases d <;> trivial
  | binary d o => intro e; cases d <;> trivial
  | lambda body => intro ⟨b,e⟩; cases b <;> trivial
  | rename f _ ih =>
    intro e
    have ht := (outer_equiv _ (f.edge_label (f.edges.invFun e))).mp (ih _)
    simpa [f.edges.right_inv] using ht

theorem iso_iff {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (f : DeepIso G H) : Copyable G ↔ Copyable H :=
  ⟨Copyable.rename f,Copyable.rename f.symm⟩

/-- Literal abstraction translation factors into a copyable payload followed by
single-use distributors, exactly as Figure 16 requires. -/
theorem abstraction_factor {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Translation.abstraction G = Serial.net (lambdaPayload G) (Translation.singleUse (d+1) k h) := rfl

/-- A payload whose box body is a language graph is globally a language graph. -/
theorem lambdaPayload_language {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    (h : Translation.LanguageGraph G) : Translation.LanguageGraph (lambdaPayload G) :=
  Serial.allLabels_net _ (Translation.allLabels_primitive _ _ _ trivial) (Translation.lambdaBox_language h)

end Copyable
end Hypernets.Copying

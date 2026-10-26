import Hypernets.Copying.ApplicationFrame

/-! Figure 10(b), with Definition 12.1's stable argument premise. Opening a box
raises only its representation allowance; it does not substitute or copy its body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

/-- The local lambda and its original box; outer translation distributors stay in the context. -/
def closure {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.term] (environmentInterface k h) :=
  Serial.net (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox B)

/-- The application head connects to the lambda and the stable argument in order. -/
def before {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Hypernet (d+1) [.term] (environmentInterface k h ++ O) :=
  Serial.net (primitiveNet (d+1) (.operation .app)) (Net.Tensor.net (closure B) G)

/-- Expose the bound output first, retaining every edge and nested box of the body. -/
def openBody {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.term] (.term :: environmentInterface k h) :=
  Translation.castInterfaces rfl (by simp [environmentInterface,List.replicate_succ]) (raise d B)

/-- Only bound output zero is connected to G. All free outputs remain external. -/
def after {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Hypernet (d+1) [.term] (environmentInterface k h ++ O) :=
  splice (openBody B) G

/-- Call-by-value stability is mandatory, including for unused arguments. -/
inductive Rule : {d k h : Nat} → {O : List Wire} →
    Hypernet (d+1) [.term] (environmentInterface k h ++ O) →
    Hypernet (d+1) [.term] (environmentInterface k h ++ O) → Prop where
  | beta {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
      (G : Hypernet (d+1) [.term] O) (stable : Stable G) : Rule (before B G) (after B G)

theorem rule_iff {d k h O} {L R : Hypernet (d+1) [.term] (environmentInterface k h ++ O)} :
    Rule L R ↔ ∃ B G, Stable G ∧ L = before (d := d) (k := k) (h := h) B G ∧ R = after B G := by
  constructor
  · intro h; cases h with | beta B G stable => exact ⟨B,G,stable,rfl,rfl⟩
  · rintro ⟨B,G,stable,rfl,rfl⟩; exact .beta B G stable

/-- The argument retains its original edge identities, including store references. -/
def argumentEdge {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : G.Edge) : (after B G).Edge := ⟨true,e⟩
def bodyEdge {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : (openBody B).Edge) : (after B G).Edge := ⟨false,e⟩
theorem argument_label {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : G.Edge) :
    (after B G).edgeLabel (argumentEdge B G e) = G.edgeLabel e := rfl
theorem body_label {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : (openBody B).Edge) :
    (after B G).edgeLabel (bodyEdge B G e) = (openBody B).edgeLabel e := rfl
theorem argument_injective {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Function.Injective (argumentEdge B G) := by
  intro e f eq; exact eq_of_heq (Sigma.mk.inj eq).2
theorem body_injective {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Function.Injective (bodyEdge B G) := by
  intro e f eq; exact eq_of_heq (Sigma.mk.inj eq).2
theorem components_disjoint {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : (openBody B).Edge) (f : G.Edge) :
    bodyEdge B G e ≠ argumentEdge B G f := by intro eq; cases congrArg Sigma.fst eq
end Hypernets.Copying.Application

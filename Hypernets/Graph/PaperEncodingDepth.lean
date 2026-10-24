import Hypernets.Graph.PaperEncoding

/-! Direct promotion of actual graph-labelled presentations, without renaming. -/
namespace Hypernets.Linear.PaperEncoding
open Graph
variable {Op : Type} (ops : Operations Op)

/-- Promote the alphabet by recursively promoting actual box contents. The
input names are retained, so the external signatures are retained as well. -/
noncomputable def raiseMap : (n : Nat) → AlphabetMap (alphabet ops n) (alphabet ops (n+1))
  | 0 => ⟨fun p => .inl p.down,fun _ => rfl,fun _ => rfl⟩
  | n+1 => {
      symbol p := match p with
        | .inl p => .inl p
        | .inr c => .inr ⟨⟨c.val.1,c.val.2.relabel _ (raiseMap n).symbol
            (raiseMap n).input (raiseMap n).output⟩,c.property⟩
      input := by intro p; cases p <;> rfl
      output := by intro p; cases p <;> rfl
    }

/-- A larger depth allowance changes labels recursively but no vertex names. -/
noncomputable def raise (n : Nat) {I O} (G : Hypernet ops n I O) : Hypernet ops (n+1) I O :=
  G.relabel _ (raiseMap ops n).symbol (raiseMap ops n).input (raiseMap ops n).output

/-- Freshening commutes exactly with increasing the depth allowance. -/
theorem encode_raise (n a b : Nat) {I O} (G : Linear.Hypernet ops n I O) :
    encode ops (n+1) a b (Linear.raise ops n G) = raise ops n (encode ops n a b G) := by
  induction n generalizing I O a b with
  | zero => rfl
  | succ n ih =>
    let φ : (Linear.alphabet ops (n+1)).Symbol → (alphabet ops (n+2)).Symbol := fun p =>
      (encodeMap ops (n+2)).symbol (match p with
        | .inl p => .inl p
        | .inr c => .inr ⟨c.bound,c.free,Linear.raise ops n c.body⟩)
    let ψ : (Linear.alphabet ops (n+1)).Symbol → (alphabet ops (n+2)).Symbol := fun p =>
      (raiseMap ops (n+1)).symbol ((encodeMap ops (n+1)).symbol p)
    have hiφ : ∀ p, (alphabet ops (n+2)).signature.input (φ p) = (Linear.alphabet ops (n+1)).signature.input p := by
      intro p; cases p <;> rfl
    have hoφ : ∀ p, (alphabet ops (n+2)).signature.output (φ p) = (Linear.alphabet ops (n+1)).signature.output p := by
      intro p; cases p <;> rfl
    have hiψ : ∀ p, (alphabet ops (n+2)).signature.input (ψ p) = (Linear.alphabet ops (n+1)).signature.input p := by
      intro p; cases p <;> rfl
    have hoψ : ∀ p, (alphabet ops (n+2)).signature.output (ψ p) = (Linear.alphabet ops (n+1)).signature.output p := by
      intro p; cases p <;> rfl
    change NamedNet.ofSet (G.toSet.relabel _ φ hiφ hoφ) a b =
      (NamedNet.ofSet (G.toSet.relabel _ (encodeMap ops (n+1)).symbol
        (encodeMap ops (n+1)).input (encodeMap ops (n+1)).output) a b).relabel _
        (raiseMap ops (n+1)).symbol (raiseMap ops (n+1)).input (raiseMap ops (n+1)).output
    rw [← NamedNet.ofSet_relabel]
    apply congrArg (fun Q : SetNet (alphabet ops (n+2)).signature I O => NamedNet.ofSet Q a b)
    change G.toSet.relabel _ φ hiφ hoφ = G.toSet.relabel _ ψ hiψ hoψ
    apply SetNet.relabel_congr
    intro p
    cases p with
    | inl p => rfl
    | inr c =>
      apply congrArg Sum.inr
      apply Subtype.ext
      apply congrArg (Sigma.mk (c.bound+c.free))
      exact ih c.bound c.free c.body

/-- Repeated direct promotion of the actual-content representation. -/
noncomputable def raiseBy (n : Nat) : (k : Nat) → {I O : List Wire} → Hypernet ops n I O → Hypernet ops (n+k) I O
  | 0,_,_,G => G
  | k+1,_,_,G => raise ops (n+k) (raiseBy n k G)

/-- Encoding commutes with every finite depth increase, not merely one layer. -/
theorem encode_raiseBy (n k a b : Nat) {I O} (G : Linear.Hypernet ops n I O) :
    encode ops (n+k) a b (SetHierarchy.typedRaiseBy ops n k G) =
      raiseBy ops n k (encode ops n a b G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change encode ops (n+k+1) a b (Linear.raise ops (n+k) (SetHierarchy.typedRaiseBy ops n k G)) = _
    rw [encode_raise,ih]; rfl

end Hypernets.Linear.PaperEncoding

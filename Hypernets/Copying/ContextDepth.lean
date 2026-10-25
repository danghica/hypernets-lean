import Hypernets.Copying.TermContextCongruence
import Hypernets.Copying.ObservationPaddingExamples

/-! Exact numeric allowances of the unchanged context interpretation. These
laws do not identify graphs that differ by padding. -/
namespace Hypernets.Copying
namespace TermContext

/-- The exact outer allowance selected by the original constructor interpreter. -/
def depthAt {v a k h} (C : TermContext v a k h) (d : Nat) : Nat :=
  match C with
  | .hole => d
  | .lam C => C.depthAt d + 1
  | .unary _ C => C.depthAt d
  | .appLeft C t | .binaryLeft _ C t => max (C.depthAt d) (Translation.depth t)
  | .appRight t C | .binaryRight _ t C => max (Translation.depth t) (C.depthAt d)

/-- This numeric function agrees with the actual original graph interpreter. -/
theorem depth_apply {v a k h} (C : TermContext v a k h)
    (G : ContextTranslation.ScopedGraph v a) :
    (ContextTranslation.apply C G).1 = C.depthAt G.1 := by
  induction C <;> simp_all [depthAt,ContextTranslation.apply,ContextTranslation.abstraction,
    ContextTranslation.unary,ContextTranslation.application,ContextTranslation.binary,ContextTranslation.ofTerm]

/-- Filling a term has the corresponding exact original minimal depth. -/
theorem depth_fill {v a k h} (C : TermContext v a k h) (t : Term v a) :
    Translation.depth (C.fill t) = C.depthAt (Translation.depth t) := by
  have eq := depth_apply C (ContextTranslation.ofTerm t)
  rw [ContextTranslation.apply_ofTerm] at eq
  exact eq

/-- Contexts never reduce the input's required allowance. -/
theorem le_depthAt {v a k h} (C : TermContext v a k h) (d : Nat) : d ≤ C.depthAt d := by
  induction C <;> simp_all only [depthAt] <;> omega

/-- Raising the input allowance cannot lower the resulting host allowance. -/
theorem depthAt_mono {v a k h} (C : TermContext v a k h) {d e : Nat} (bound : d ≤ e) :
    C.depthAt d ≤ C.depthAt e := by
  induction C <;> simp_all only [depthAt] <;> omega

/-- Increasing the input allowance by n adds at most n to the host allowance;
fixed siblings can absorb some or all of the increase at maximum-depth joins. -/
theorem depthAt_add_le {v a k h} (C : TermContext v a k h) (d n : Nat) :
    C.depthAt (d+n) ≤ C.depthAt d+n := by
  induction C <;> simp_all only [depthAt] <;> omega
end TermContext

namespace Examples
/-- The original allocation/let program genuinely has the larger minimal depth. -/
theorem privateCell_depth (k h : Nat) : Translation.depth (Term.privateCell k h) = 3 := rfl

/-- The original constant-result program has minimal depth two. -/
theorem constantResult_depth (k h : Nat) : Translation.depth (Term.constantResult k h) = 2 := rfl

/-- Equal-depth contextual congruence alone does not cover the proposition's
unchanged programs; the unequal-depth padding comparison is a real obligation. -/
theorem proposition12_2_depths_differ (k h : Nat) :
    Translation.depth (Term.privateCell k h) ≠ Translation.depth (Term.constantResult k h) := by
  rw [privateCell_depth,constantResult_depth]
  decide
end Examples
end Hypernets.Copying

import Hypernets.Copying.ContextFilling
import Hypernets.Copying.ParallelFillingExamples

/-! Regressions for the complete context grammar with depth-unequal branches. -/
namespace Hypernets.Copying.Examples

/-- A fixed sibling with two boxes, in arbitrary ambient environments. -/
def twoBoxSibling (k h : Nat) : Term k h := .lam (.lam (.var 0))

/-- Every constructor appears on the path to the hole, including both argument
positions. The hole can refer to the variable bound by the outer lambda. -/
def mixedArgumentContext (k h : Nat) : TermContext (k+1) h k h :=
  .lam (.unary .deref
    (.appLeft
      (.binaryRight .add (twoBoxSibling (k+1) h)
        (.appRight (twoBoxSibling (k+1) h)
          (.binaryLeft .assign .hole (.const .unit))))
      (twoBoxSibling (k+1) h)))

/-- A zero-depth hole encounters a depth-two sibling, exercising a genuine
maximum-depth padding branch; the surrounding lambda adds one more level. -/
theorem mixedArgumentContext_depth (k h name : Nat) :
    (ContextTranslation.graph (mixedArgumentContext k h) 0 name).1 = 3 := rfl

/-- Substituting a term retains exactly the original constructor expression. -/
theorem mixedArgumentContext_fill (k h : Nat) (t : Term (k+1) h) :
    (mixedArgumentContext k h).fill t =
      .lam (.unary .deref
        (.app (.binary .add (twoBoxSibling (k+1) h)
          (.app (twoBoxSibling (k+1) h) (.binary .assign t (.const .unit))))
          (twoBoxSibling (k+1) h))) := rfl

/-- Actual filling reconstructs the direct original translation in the mixed
context for every argument term, variable environment and atom environment. -/
theorem mixedArgumentContext_graph_filling (k h name : Nat) (t : Term (k+1) h) :
    ∃ n, ∃ s : Site (ContextTranslation.graph (mixedArgumentContext k h) (Translation.depth t) name).2
        (Translation.depth t+n) [.term] (environmentInterface (k+1) h),
      SoleHole s ∧ BindingFree (ContextTranslation.graph (mixedArgumentContext k h) (Translation.depth t) name).2 ∧
      ContextTranslation.ScopedIso
        ⟨(ContextTranslation.graph (mixedArgumentContext k h) (Translation.depth t) name).1,
          plugAt s (Translation.pad (Translation.depth t) n (Translation.term t))⟩
        (ContextTranslation.ofTerm ((mixedArgumentContext k h).fill t)) :=
  ContextTranslation.context_term_filling _ name t
end Hypernets.Copying.Examples

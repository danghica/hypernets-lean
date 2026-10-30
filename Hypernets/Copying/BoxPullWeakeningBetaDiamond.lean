import Hypernets.Copying.BoxPullWeakeningBeta
import Hypernets.Copying.BoxPullWeakeningOpening
import Hypernets.Copying.FillingAssembly
import Hypernets.Copying.EqualPrefixCosts

/-! A complete actual local beta diamond for the literal BPullW family.
The source has a genuine template filling certificate; both sides take the
original beta transition, and their successors are recursively isomorphic. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

def splice_output {d F K O} (G : Hypernet d [.term] (.term :: F))
    (V : Hypernet d [.term] O) (eq : F = K) :
    DeepIso (Application.splice (G.reboundary rfl (congrArg (List.cons Wire.term) eq)) V)
      ((Application.splice G V).reboundary rfl (congrArg (fun X => X ++ O) eq)) := by
  cases eq
  simpa only [Net.reboundary_refl] using DeepIso.refl (Application.splice G V)

def boxedApplication_output {d F K O} (X : Hypernet (d+1) [.thunk 1] F)
    (V : Hypernet (d+1) [.term] O) (eq : F = K) :
    DeepIso (boxedApplication (X.reboundary rfl eq) V)
      ((boxedApplication X V).reboundary rfl (congrArg (fun F => F ++ O) eq)) := by
  cases eq
  simpa only [Net.reboundary_refl] using DeepIso.refl (boxedApplication X V)

def outsideBetaSource {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) :
    Hypernet (d+1) [.term] (environmentInterface (variables s k) (atoms s h) ++ O) :=
  (boxedApplication (adjoin (Translation.lambdaBox B) s) V).reboundary rfl
    (congrArg (fun F => F ++ O) (adjoin_interface s k h))

def outsideBetaAfter {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) :
    Hypernet (d+1) [.term] (environmentInterface (variables s k) (atoms s h) ++ O) :=
  (Splice.right (A := List.replicate k .term) (B := List.replicate h .atom)
    (Application.openBody B) V s).reboundary rfl
    (congrArg (fun F => F ++ O) (adjoin_interface s k h))

/-- The raw outside box is only recast to the paper's counted environment. -/
def outsideBetaSource_iso {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) :
    DeepIso (boxedApplication (extend (Translation.lambdaBox B) s) V) (outsideBetaSource B V s) := by
  rw [extend_eq]
  exact boxedApplication_output _ _ _

/-- This is the actual original recursive template certificate at the source,
with the app, lambda and stable argument retained in the shared context. -/
noncomputable def beta_sourceWitness {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort)
    (free : FocusFree B) (stable : Stable V) :
    FillingWitness template (Application.before (betaBody B s) V) (outsideBetaSource B V s) := by
  let boxPair := FillingWitness.of_rel 0 (lambda_literal B s free)
  let closure := (FillingWitness.refl (primitiveNet (d+1) (.operation .lam))
    (by intro e m eq; cases eq)).serial boxPair
  let operands := closure.tensor (FillingWitness.refl V stable.focusFree)
  let full := (FillingWitness.refl (primitiveNet (d+1) (.operation .app))
    (by intro e m eq; cases eq)).serial operands
  exact full.congr (DeepIso.refl _) (outsideBetaSource_iso B V s)

/-- Both reducts keep the same bound-output junction and every original body
and argument edge. Their only difference is finite carrier association. -/
def beta_successorIso {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) :
    DeepIso (Application.after (betaBody B s) V) (outsideBetaAfter B V s) := by
  unfold Application.after
  rw [open_betaBody]
  exact (splice_output _ V (adjoin_interface s k h)).trans
    (CopyRule.reboundaryIso (Splice.iso (Application.openBody B) V s) rfl
      (congrArg (fun F => F ++ O) (adjoin_interface s k h)))

/-- The full local beta diamond, with the original stability premise and
exact active and resumed token positions on both sides. -/
theorem beta_diamond {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) (stable : Stable V) :
    Rewrite (Application.before (betaBody B s) V) (.input 0)
      (Application.after (betaBody B s) V) (.input 0) ∧
    Rewrite (outsideBetaSource B V s) (.input 0) (outsideBetaAfter B V s) (.input 0) ∧
    Nonempty (DeepIso (Application.after (betaBody B s) V) (outsideBetaAfter B V s)) :=
  ⟨.local (.beta _ V stable),
    rewrite_reboundary rfl (congrArg (fun F => F ++ O) (adjoin_interface s k h))
      (outside_beta B V s stable), ⟨beta_successorIso B V s⟩⟩

/-- The completed shallow beta case preserves every successful transition
count in every typed surrounding graph, including contexts in which the
opened body or callback diverges. The focus is at this actual beta redex. -/
theorem beta_costs_at {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (V : Hypernet (d+1) [.term] O) (s : ShareSort) (stable : Stable V)
    {I J} (C : Hypernet (d+1) I J) (e : C.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface (variables s k) (atoms s h) ++ O =
      (alphabet (d+1)).signature.output (C.edgeLabel e)) (cost : Nat) :
    TerminatesIn cost (plugState C e (Combined.castInterfaces hi ho
      ⟨Application.before (betaBody B s) V,(.rewrite,.input 0)⟩)) ↔
    TerminatesIn cost (plugState C e (Combined.castInterfaces hi ho
      ⟨outsideBetaSource B V s,(.rewrite,.input 0)⟩)) :=
  equal_prefix_costs_at C e hi ho
    (.cons (.rewrite (beta_diamond B V s stable).1) (.zero _))
    (.cons (.rewrite (beta_diamond B V s stable).2.1) (.zero _))
    ⟨beta_successorIso B V s,rfl,rfl⟩ cost

end Hypernets.Copying.BoxPullWeakening

import Hypernets.Copying.BoxPullContractionBeta
import Hypernets.Copying.BoxPullContractionOpening
import Hypernets.Copying.BoxPullWeakeningBetaDiamond

/-! The complete literal BPullC beta diamond: original stable beta steps on
both sides, followed by exact recursive graph isomorphism of the successors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction
open Graph Combined

abbrev two_interface (s : ShareSort) (k h : Nat) :
    environmentInterface (variables s k 2) (atoms s h 2) =
      List.replicate k .term ++ s.wire :: s.wire :: List.replicate h .atom := by
  simpa using block_interface s k h 2

abbrev one_interface (s : ShareSort) (k h : Nat) :
    List.replicate k .term ++ s.wire :: List.replicate h .atom =
      environmentInterface (variables s k 1) (atoms s h 1) := by
  simpa using (block_interface s k h 1).symm

abbrev rawOpen {d k h} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2))) :=
  (Application.openBody G).reboundary rfl (congrArg (List.cons Wire.term) (two_interface s k h))

def outsideBetaSource {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) :
    Hypernet (d+1) [.term] (environmentInterface (variables s k 1) (atoms s h 1) ++ O) :=
  (boxedApplication (merge s ((Translation.lambdaBox G).reboundary rfl (two_interface s k h))) V).reboundary
    rfl (congrArg (fun F => F ++ O) (one_interface s k h))

def outsideBetaAfter {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) :
    Hypernet (d+1) [.term] (environmentInterface (variables s k 1) (atoms s h 1) ++ O) :=
  ((merge (A := List.replicate k .term) (B := List.replicate h .atom ++ O) s
    ((Application.after G V).reboundary rfl ((congrArg (fun F => F ++ O) (two_interface s k h)).trans
      (by simp only [List.append_assoc,List.cons_append])))).reboundary
      rfl (by simp only [List.append_assoc,List.cons_append])).reboundary
        rfl (congrArg (fun F => F ++ O) (one_interface s k h))

/-- The source is exactly a literal template occurrence within the original
app/lam prefix and stable argument context. -/
noncomputable def beta_sourceWitness {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) (free : FocusFree G) (stable : Stable V) :
    FillingWitness template (Application.before (betaBody s G) V) (outsideBetaSource s G V) := by
  let boxPair := FillingWitness.of_rel 0 (lambda_literal s G free)
  let closure := (FillingWitness.refl (primitiveNet (d+1) (.operation .lam))
    (by intro e m eq; cases eq)).serial boxPair
  let operands := closure.tensor (FillingWitness.refl V stable.focusFree)
  let full := (FillingWitness.refl (primitiveNet (d+1) (.operation .app))
    (by intro e m eq; cases eq)).serial operands
  refine full.congr (DeepIso.refl _) ?_
  change DeepIso (boxedApplication (contract s (Translation.lambdaBox G)) V) _
  rw [contract_eq]
  exact boxedApplication_output _ _ _

/-- Recasting the free interface commutes with the original body--argument
splice, and hence the raw outside successor is exactly the original beta
successor with its external contraction retained. -/
def raw_successorIso {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) :
    DeepIso ((Splice.right s (rawOpen s G) V).reboundary rfl
      (congrArg (fun F => F ++ O) (one_interface s k h))) (outsideBetaAfter s G V) := by
  have first := BoxPullWeakening.splice_output (Application.openBody G) V (two_interface s k h)
  have first := CopyRule.reboundaryIso first rfl
    (show (List.replicate k .term ++ s.wire :: s.wire :: List.replicate h .atom) ++ O =
      List.replicate k .term ++ s.wire :: s.wire :: (List.replicate h .atom ++ O) from by
        simp only [List.append_assoc,List.cons_append])
  rw [reboundary_comp] at first
  exact CopyRule.reboundaryIso (CopyRule.reboundaryIso (merge_congr s first) rfl
    (by simp only [List.append_assoc,List.cons_append])) rfl
      (congrArg (fun F => F ++ O) (one_interface s k h))

/-- All original body and argument edges and the bound-output junction are
preserved; only the finite carrier grouping differs between the reducts. -/
noncomputable def beta_successorIso {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) :
    DeepIso (Application.after (betaBody s G) V) (outsideBetaAfter s G V) :=
  (Application.splice_congr (open_betaBody s G) (DeepIso.refl V)).trans
    ((BoxPullWeakening.splice_output _ V (one_interface s k h)).trans
      ((CopyRule.reboundaryIso (Splice.iso s (rawOpen s G) V) rfl
        (congrArg (fun F => F ++ O) (one_interface s k h))).trans (raw_successorIso s G V)))

/-- Both branches take the actual original beta rule at the same input and
resume at that input, preserving the original stable-argument premise. -/
theorem beta_diamond {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) (stable : Stable V) :
    Rewrite (Application.before (betaBody s G) V) (.input 0)
      (Application.after (betaBody s G) V) (.input 0) ∧
    Rewrite (outsideBetaSource s G V) (.input 0) (outsideBetaAfter s G V) (.input 0) ∧
    Nonempty (DeepIso (Application.after (betaBody s G) V) (outsideBetaAfter s G V)) :=
  ⟨.local (.beta _ V stable),
    rewrite_reboundary rfl (congrArg (fun F => F ++ O) (one_interface s k h))
      (outside_beta s G V stable (two_interface s k h)), ⟨beta_successorIso s G V⟩⟩

/-- Exact transition-count equivalence for the completed local beta overlap
in every typed host, including diverging opened bodies or callbacks. -/
theorem beta_costs_at {d k h O} (s : ShareSort)
    (G : Hypernet d [.term] (environmentInterface (variables s k 2+1) (atoms s h 2)))
    (V : Hypernet (d+1) [.term] O) (stable : Stable V)
    {I J} (C : Hypernet (d+1) I J) (e : C.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (C.edgeLabel e))
    (ho : environmentInterface (variables s k 1) (atoms s h 1) ++ O =
      (alphabet (d+1)).signature.output (C.edgeLabel e)) (cost : Nat) :
    TerminatesIn cost (plugState C e (Combined.castInterfaces hi ho
      ⟨Application.before (betaBody s G) V,(.rewrite,.input 0)⟩)) ↔
    TerminatesIn cost (plugState C e (Combined.castInterfaces hi ho
      ⟨outsideBetaSource s G V,(.rewrite,.input 0)⟩)) :=
  equal_prefix_costs_at C e hi ho
    (.cons (.rewrite (beta_diamond s G V stable).1) (.zero _))
    (.cons (.rewrite (beta_diamond s G V stable).2.1) (.zero _))
    ⟨beta_successorIso s G V,rfl,rfl⟩ cost

end Hypernets.Copying.BoxPullContraction

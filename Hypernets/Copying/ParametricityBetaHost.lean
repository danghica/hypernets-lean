import Hypernets.Copying.CommonContextOpening
import Hypernets.Copying.CommonContextExecution
import Hypernets.Copying.ParametricityCommonRead
import Hypernets.Copying.RootedOpeningRewrite

/-! Whole-host transport of the genuine private-read beta diagram. The
argument may itself be a shallow parametricity family: it stays entirely in
the common complement, and original rooted readiness enables both beta rules. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.BetaHost
open Graph Opening Combined CommonContextCut
open BoxPullWeakening (PointedWitness)
variable {d} (C : Hypernet (d+1) [.term] []) {J K} {A : Hypernet (d+1) J K}
    (f : Occurrence A C) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L))
    {a : A.Vertex}
    (leftRoot : Search.RootedFrom (C.expand L) 0 (.rewrite,Net.Expansion.host C L (f.ports a)))
    (rightRoot : Search.RootedFrom (C.expand R) 0 (.rewrite,Net.Expansion.host C R (f.ports a)))
    {k h k' h'} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {D : Hypernet d [.term] (environmentInterface (k'+1) h')}
    {X Y Z W : Hypernet (d+1) J K} {x : X.Vertex} {y : Y.Vertex} {z : Z.Vertex} {w : W.Vertex}
    (leftOpening : Application.OpeningCertificate ((skeleton C f).expand (localFamily C f L)) X
      (Net.Expansion.host (skeleton C f) (localFamily C f L) a) x B)
    (rightOpening : Application.OpeningCertificate ((skeleton C f).expand (localFamily C f R)) Y
      (Net.Expansion.host (skeleton C f) (localFamily C f R) a) y D)
    {n} (run : (machine (d+1) J K).Steps n ⟨X,(.search,x)⟩ ⟨Z,(.search,z)⟩)
    (correction : ReadResidual Z z W w) (paired : PointedWitness template W w Y y)
    (typed : Z.vertexLabel z = .term)
include cert free leftClosed leftRoot rightRoot leftOpening rightOpening run correction paired typed

/-- The complete actual host has one beta plus the literal post-opening run
on the left, one beta on the right, and the paper's directed quasi-specimen
in both orientations. Every correction and its intermediate root is proved. -/
theorem diagram :
    ∃ s t, StateClass.machine.Steps (n+1)
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports a))⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines CostOrder.improvement) Eq s t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        Eq (StateClass.machine.Refines CostOrder.overhead) t s := by
  have left := (opening_at C f L leftOpening).rooted_rewrite leftRoot
  have right := (opening_at C f R rightOpening).rooted_rewrite rightRoot
  have tail := after_run C f L run
  have whole : (machine (d+1) [.term] []).Steps (n+1)
      ⟨C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩
      (afterState C f L ⟨Z,(.search,z)⟩) := .cons (.rewrite left) tail
  have closed : HoleFree (afterGraph C f L Z) :=
    run_allLabels _ RuleSafety.admits_holeFree tail (rewrite_holeFree left leftClosed)
  have fillFree (e : C.Edge) : FocusFree (L e) := (FillingWitness.of_edge (cert e) free).focusFree.1
  let p := readResidual C f L fillFree correction
  let q := pairedPointed C f cert free paired
  have actualTyped := (after_label C f L Z z).trans typed
  exact ⟨_,_,StateClass.project_run (run_unbounded whole),StateClass.project (.lift (.rewrite right)),
    p.parametricity_quasi q closed actualTyped,p.parametricity_quasi_converse q closed actualTyped⟩

/-- Any independently presented left successor has the full forward clause;
its first transition is identified using the already proved machine coherence. -/
theorem forward_case (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩) successor) :
    ∃ k l s t, CostOrder.improvement.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports a))⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines CostOrder.improvement) (StateClass.machine.Refines U) s t := by
  obtain ⟨s,t,left,right,pair,_⟩ := diagram C f cert free leftClosed leftRoot rightRoot
    leftOpening rightOpening run correction paired typed
  cases left with
  | cons first rest =>
    have eq := StateClass.machine_deterministic step first
    refine ⟨n,1,s,t,?_,eq ▸ rest,.cons right (.zero _),?_⟩
    · change 1 ≤ 1+n; omega
    · intro lr rr
      obtain ⟨S,mode,sl,sr,l,r⟩ := pair lr rr
      refine ⟨S,mode,sl,sr,l,?_⟩
      rw [r]
      exact Machine.Refines.refl U _

/-- The independently presented converse successor uses one-versus-(n+1)
actual transitions and retains the opposite quantitative inequality. -/
theorem converse_case (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports a))⟩) successor) :
    ∃ k l s t, CostOrder.overhead.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports a))⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines CostOrder.overhead) s t := by
  obtain ⟨s,t,left,right,_,pair⟩ := diagram C f cert free leftClosed leftRoot rightRoot
    leftOpening rightOpening run correction paired typed
  have eq := StateClass.machine_deterministic step right
  refine ⟨0,n+1,t,s,?_,eq ▸ .zero _,left,?_⟩
  · change 1 ≤ n+1; omega
  · intro rr lr
    obtain ⟨S,mode,sr,sl,r,l⟩ := pair rr lr
    refine ⟨S,mode,sr,sl,?_,l⟩
    rw [r]
    exact Machine.Refines.refl P _
end Hypernets.Copying.Parametricity.BetaHost

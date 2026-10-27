import Hypernets.Copying.BetaFillingWitness

/-! Original quasi-specimens and the complete robustness conclusion for closed
all-deep beta cases, with a derived right-hand stable argument. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.DeepBeta
open Graph Combined
variable {d} {B C : Hypernet d [.term] (environmentInterface 1 0)}
    {G H : Hypernet (d+1) [.term] []}

def source (B : Hypernet d [.term] (environmentInterface 1 0))
    (G : Hypernet (d+1) [.term] []) : UnboundedState :=
  ⟨d+1,Application.before B G,(.rewrite,.input 0)⟩
def target (B : Hypernet d [.term] (environmentInterface 1 0))
    (G : Hypernet (d+1) [.term] []) : UnboundedState :=
  ⟨d+1,Application.after B G,(.search,.input 0)⟩

theorem step (B : Hypernet d [.term] (environmentInterface 1 0))
    (G : Hypernet (d+1) [.term] []) (stable : Stable G) :
    StateClass.machine.step (StateClass.ofState (source B G)) (StateClass.ofState (target B G)) :=
  StateClass.project (.lift (Combined.local_step (.beta B G stable)))

/-- All nested body occurrences are retained in the exposed residual specimen. -/
theorem quasi (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) (left : HoleFree B) (right : HoleFree C) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState (target B G)) (StateClass.ofState (target C H)) :=
  (body.betaAfter template_paddingClosed arg).initial_quasi template_outputClosed
    (Application.after_labels _ B G left stable.holeFree)
    (Application.after_labels _ C H right ((arg.stable_iff template_preservesStableLabels).mp stable).holeFree)

theorem quasi_opposite (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) (left : HoleFree B) (right : HoleFree C) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi Eq Eq
      (StateClass.ofState (target C H)) (StateClass.ofState (target B G)) :=
  FillingWitness.quasi_exchange _ (quasi body arg stable left right)

/-- Every independent source successor satisfies the quantitative robustness
conclusion; k=0 and l=1 use the original beta rule on both sides. -/
theorem robust_case (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) (left : HoleFree B) (right : HoleFree C) (Q P R : CostOrder)
    {u} (next : StateClass.machine.step (StateClass.ofState (source B G)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (source C H)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R (step B G stable)
    (step C H ((arg.stable_iff template_preservesStableLabels).mp stable))
    (quasi body arg stable left right) next

theorem robust_case_opposite (body : FillingWitness template B C) (arg : FillingWitness template G H)
    (stable : Stable G) (left : HoleFree B) (right : HoleFree C) (Q P R : CostOrder)
    {u} (next : StateClass.machine.step (StateClass.ofState (source C H)) u) :
    ∃ k l a b, Q.rel (1+k) l ∧ StateClass.machine.Steps k u a ∧
      StateClass.machine.Steps l (StateClass.ofState (source B G)) b ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines R) a b :=
  FillingWitness.matching_robust_case Q P R
    (step C H ((arg.stable_iff template_preservesStableLabels).mp stable)) (step B G stable)
    (quasi_opposite body arg stable left right) next

/-- With open free interfaces, exact six-step cancellation is valid in every
typed host. The remaining residual comparison is explicit, not assumed here. -/
theorem residual_spectra_at {d k h O I J}
    {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    {G H : Hypernet (d+1) [.term] O} (body : FillingWitness template B C)
    (arg : FillingWitness template G H) (stable : Stable G)
    (K : Hypernet (d+1) I J) (e : K.Edge)
    (hi : [.term] = (alphabet (d+1)).signature.input (K.edgeLabel e))
    (ho : environmentInterface k h ++ O = (alphabet (d+1)).signature.output (K.edgeLabel e)) :
    (∀ cost, TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
        ⟨Application.before B G,(.search,.input 0)⟩)) ↔
      TerminatesIn cost (plugState K e (Combined.castInterfaces hi ho
        ⟨Application.before C H,(.search,.input 0)⟩))) ↔
    (∀ rest, TerminatesIn rest (plugState K e (Combined.castInterfaces hi ho
        ⟨Application.after B G,(.search,.input 0)⟩)) ↔
      TerminatesIn rest (plugState K e (Combined.castInterfaces hi ho
        ⟨Application.after C H,(.search,.input 0)⟩))) :=
  equal_prefix_spectra_at K e hi ho (opening body arg stable).1 (opening body arg stable).2.1
end Hypernets.Copying.BoxPermutation.DeepBeta

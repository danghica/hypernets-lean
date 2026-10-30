import Hypernets.Copying.SharingNonsharingFootprint
import Hypernets.Copying.UnrestrictedDeepLocal
import Hypernets.Copying.NullaryPrimitiveResiduals

/-! The nonsharing cases of universal sharing-template robustness. Every
original stable operand and arbitrary recursively filled beta body is retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingResidual
open Graph Combined RetainedFootprint
variable {T : PreTemplate} {d} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {v : C.Vertex}
include cert trees free leftClosed rightClosed

/-- Actual paired allocation rewrites have an equality-up-to residual,
including when the original token enters a sharing-template component. -/
theorem allocation_matching {K} (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := primitive_allContexts_input_diamond C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.allocation_nonsharing stable)) free
    (BoxPermutation.PrimitiveFootprint.allocation G stable) 0 rfl (.local (.allocate G stable))
    attached closed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),
    StateClass.project (.lift (.rewrite right)),residual⟩

/-- Actual paired unary rewrites have an equality-up-to residual,
including when the original token enters a sharing-template component. -/
theorem unary_matching {n : Nat}
    (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := primitive_allContexts_input_diamond C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.unary_nonsharing d n)) free
    (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n))
    attached closed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),
    StateClass.project (.lift (.rewrite right)),residual⟩

/-- Actual paired binary rewrites have an equality-up-to residual,
including when the original token enters a sharing-template component. -/
theorem binary_matching (op : Arithmetic.BinaryCode) {m n : Nat}
    (f : Opening.Occurrence (Arithmetic.binaryBefore op d m n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v) :
    ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  obtain ⟨left,right,residual⟩ := primitive_allContexts_input_diamond C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.binary_nonsharing op d m n)) free
    (BoxPermutation.PrimitiveFootprint.binary op d m n) 0 rfl (.local (.binaryArithmetic op d m n))
    attached closed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),
    StateClass.project (.lift (.rewrite right)),residual⟩

/-- Allocation allocates exactly the original stable operand. The entire
quantitative robustness case holds in every original common context. -/
theorem allocation {K} (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_allContexts_robust_case C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.allocation_nonsharing stable)) free
    (BoxPermutation.PrimitiveFootprint.allocation G stable) 0 rfl (.local (.allocate G stable))
    attached closed leftClosed rightClosed Q P U step

/-- The unary natural-number rule is unchanged. The entire
quantitative robustness case holds in every original common context. -/
theorem unary {n : Nat}
    (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_allContexts_robust_case C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.unary_nonsharing d n)) free
    (BoxPermutation.PrimitiveFootprint.unary d n) 0 rfl (.local (.unaryArithmetic d n))
    attached closed leftClosed rightClosed Q P U step

/-- Both ordered binary arithmetic rules use their original operands. The entire
quantitative robustness case holds in every original common context. -/
theorem binary (op : Arithmetic.BinaryCode) {m n : Nat}
    (f : Opening.Occurrence (Arithmetic.binaryBefore op d m n) (C.expand L))
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t :=
  primitive_allContexts_robust_case C f cert
    (SharingOverlap.avoids C cert trees leftClosed f (SharingOverlap.binary_nonsharing op d m n)) free
    (BoxPermutation.PrimitiveFootprint.binary op d m n) 0 rfl (.local (.binaryArithmetic op d m n))
    attached closed leftClosed rightClosed Q P U step

end Hypernets.Copying.SharingResidual

namespace Hypernets.Copying.SharingResidual
open Graph Combined RetainedFootprint

/-- Padding-closed sharing templates transport every actual beta body through
opening, without a binding-free restriction or a shallow-overlap assumption. -/
theorem beta_matching {T : PreTemplate} {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h K} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    : ∃ s t, StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi Eq Eq s t := by
  have avoid := SharingOverlap.avoids C cert trees leftClosed f
    (SharingOverlap.beta_nonsharing B stable)
  obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.beta_local C cert padding free B G stable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free 0 rfl
    (.local (.beta B G stable)) paired w attached closed leftClosed rightClosed
  exact ⟨_,_,StateClass.project (.lift (.rewrite left)),
    StateClass.project (.lift (.rewrite right)),residual⟩


/-- Padding-closed sharing templates transport every actual beta body through
opening, without a binding-free restriction or a shallow-overlap assumption. -/
theorem beta {T : PreTemplate} {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (padding : T.PaddingClosed) (free : FocusFree C) (closed : T.OutputClosed)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    {k h K} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] K) (stable : Stable G)
    (f : Opening.Occurrence (Application.before B G) (C.expand L)) {v : C.Vertex}
    (attached : f.ports (.input 0) = Net.Expansion.host C L v)
    (Q P U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,(.rewrite,Net.Expansion.host C L v)⟩) successor) :
    ∃ k l s t, Q.rel (1+k) l ∧ StateClass.machine.Steps k successor s ∧
      StateClass.machine.Steps l
        (StateClass.ofState ⟨d+1,C.expand R,(.rewrite,Net.Expansion.host C R v)⟩) t ∧
      (Specimens.system T Specimens.allContexts closed).Quasi
        (StateClass.machine.Refines P) (StateClass.machine.Refines U) s t := by
  have avoid := SharingOverlap.avoids C cert trees leftClosed f
    (SharingOverlap.beta_nonsharing B stable)
  obtain ⟨H,paired,⟨w⟩⟩ := UnrestrictedResidual.beta_local C cert padding free B G stable f avoid
  obtain ⟨left,right,residual⟩ := allContexts_input_diamond C f cert avoid free 0 rfl
    (.local (.beta B G stable)) paired w attached closed leftClosed rightClosed
  exact FillingWitness.matching_robust_case Q P U
    (StateClass.project (.lift (.rewrite left))) (StateClass.project (.lift (.rewrite right))) residual step

end Hypernets.Copying.SharingResidual

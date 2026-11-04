import Hypernets.Copying.RetainedBetaOpening
import Hypernets.Copying.UnrestrictedLocalViews
import Hypernets.Copying.BetaFillingWitness

/-! The retained three-edge frame has a paired original boxed body while
all stable-argument contributions remain outside the footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening
variable {T : PreTemplate} {d k h}
    (B C : Hypernet d [.term] (environmentInterface (k+1) h))

/-- Change just the box label, retaining the exact app/lambda wiring. -/
def changedFill (e : (net B).Edge) : Hypernet (d+1)
    ((alphabet (d+1)).signature.input ((net B).edgeLabel e))
    ((alphabet (d+1)).signature.output ((net B).edgeLabel e)) := by
  cases e
  · exact Net.corolla (alphabet (d+1)).signature (label C .app)
  · exact Net.corolla (alphabet (d+1)).signature (label C .lam)
  · exact Net.corolla (alphabet (d+1)).signature (label C .box)

def changedCopy (e : (net B).Edge) : LabelCopy (changedFill B C e) (label C e) := by
  cases e <;> exact LabelCopy.corolla _

/-- Corolla expansion collapses to the exact three-edge frame with its
paired body. The boundary order, argument output and free outputs are fixed. -/
noncomputable def changedIso : DeepIso ((net B).expand (changedFill B C)) (net C) :=
  DeepIso.ofIso (FillingCollapse.relabel (net B) (changedFill B C) (label C) (changedCopy B C)
    (by intro e; cases e <;> rfl) (by intro e; cases e <;> rfl))

variable (D : UnrestrictedDecoration T (net B))

/-- The primitive app and lambda copies collapse independently of any
argument. The box component uses its actual complete body isomorphism. -/
noncomputable def sourceIso (box : DeepIso (Translation.lambdaBox C) (D.fill .box)) :
    DeepIso D.graph (net C) := by
  have expanded : DeepIso D.graph ((net B).expand (changedFill B C)) := by
    apply Net.ExpansionIso.iso (net B)
    intro e
    cases e
    · exact ((D.pair .app).primitiveIso (by intro e; exact ⟨.operation .app,rfl⟩)).symm
    · exact ((D.pair .lam).primitiveIso (by intro e; exact ⟨.operation .lam,rfl⟩)).symm
    · exact box.symm
  exact expanded.trans (changedIso B C)

/-- The original retained/deep certificate produces a genuine body filling,
not a conditional translation assumption or isolated argument equivalence. -/
theorem paired_body (free : FocusFree (net B)) :
    ∃ C : Hypernet d [.term] (environmentInterface (k+1) h),
      Nonempty (FillingWitness T B C) ∧ Nonempty (DeepIso D.graph (net C)) := by
  have bodyFree : FocusFree B :=
    (Translation.allLabels_cast _ rfl (congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)) B).mp (free .box)
  cases (D.pair .box).lambdaView with
  | retained iso => exact ⟨B,⟨FillingWitness.refl B bodyFree⟩,⟨sourceIso B B D iso⟩⟩
  | @deep C H body iso => exact ⟨C,⟨body⟩,⟨sourceIso B C D iso⟩⟩

/-- The paired local opening certificate exposes the actual padded body;
the argument wire stays an external output of the frame on both sides. -/
theorem paired_opening (padding : T.PaddingClosed) (free : FocusFree (net B)) :
    ∃ C : Hypernet d [.term] (environmentInterface (k+1) h),
      Nonempty (OpeningCertificate D.graph (openBody C)
        (Net.Expansion.host (net B) D.fill (.input 0)) (.input 0) C) ∧
      Nonempty (FillingWitness T (openBody B) (openBody C)) := by
  obtain ⟨C,⟨body⟩,⟨iso⟩⟩ := paired_body B D free
  exact ⟨C,⟨(certificate C).rename iso.symm (DeepIso.refl _)⟩,⟨body.openBody padding⟩⟩

end Hypernets.Copying.Application.RetainedFrame

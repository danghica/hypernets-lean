import Hypernets.Copying.CopyingInputWitness
import Hypernets.Copying.SharingTreeAlgebra

/-! Reverse a genuine recursive filling only when its underlying template
relation has a proved symmetry. This applies to the sharing correction, not
to the directed copying pre-template itself. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem DeepFilling.reverse {T : PreTemplate}
    (symmetric : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → T.Rel H G)
    {d I O} {C G H : Hypernet d I O} (w : DeepFilling T C G H) : DeepFilling T C H G := by
  induction d generalizing I O with
  | zero =>
    cases w with
    | expand C L R cert =>
      apply DeepFilling.expand C R L
      intro e
      cases cert e with
      | retained l r => exact .retained r l
      | filled h label rel => exact .filled h label (symmetric rel)
  | succ d ih =>
    cases w with
    | expand C L R cert =>
      apply DeepFilling.expand C R L
      intro e
      cases cert e with
      | retained l r => exact .retained r l
      | filled h label rel => exact .filled h label (symmetric rel)
      | boxed b label inner l r => exact .boxed b label (ih inner) r l

noncomputable def FillingWitness.reverse {T : PreTemplate}
    (symmetric : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H → T.Rel H G)
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H) : FillingWitness T H G :=
  FillingWitness.ofDeepFilling w.free (w.paired.reverse symmetric) w.rightIso w.leftIso

noncomputable def FillingWitness.reverseSharing {d I O} {G H : Hypernet d I O}
    (w : FillingWitness SharingTreeAlgebra.template G H) :
    FillingWitness SharingTreeAlgebra.template H G :=
  w.reverse (T := SharingTreeAlgebra.template) (fun pair => SharingTreePair.converse pair)

end Hypernets.Copying

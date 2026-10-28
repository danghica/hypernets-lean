import Hypernets.Copying.DeepFillings

/-! Reversing a structural filling certificate preserves the original context
and actual endpoint graphs, including its recursive box witnesses. -/
namespace Hypernets.Copying

/-- The same actual pairs with the endpoint order reversed. -/
def PreTemplate.converse (T : PreTemplate) : PreTemplate where
  Rel G H := T.Rel H G
  focus_free pair := ⟨(T.focus_free pair).2,(T.focus_free pair).1⟩

/-- Reversal does not choose a new context or new filling representation. -/
theorem DeepFilling.converse {T d I O} {C L R : Hypernet d I O}
    (fill : DeepFilling T C L R) : DeepFilling T.converse C R L := by
  induction d generalizing I O with
  | zero =>
    cases fill with
    | expand C L R edges =>
      apply DeepFilling.expand
      intro e
      cases edges e with
      | retained l r => exact .retained r l
      | filled h label pair => exact .filled h label pair
  | succ d ih =>
    cases fill with
    | expand C L R edges =>
      apply DeepFilling.expand
      intro e
      cases edges e with
      | retained l r => exact .retained r l
      | filled h label pair => exact .filled h label pair
      | boxed b label inner l r => exact .boxed b label (ih inner) r l

/-- Edge-level reversal exposes the same right occurrence to the generic
binding-free path barriers. -/
theorem DeepFillingEdge.converse {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) : DeepFillingEdge T.converse C R L e := by
  cases cert with
  | retained l r => exact .retained r l
  | filled h label pair => exact .filled h label pair
  | boxed b label inner l r => exact .boxed b label inner.converse r l

end Hypernets.Copying

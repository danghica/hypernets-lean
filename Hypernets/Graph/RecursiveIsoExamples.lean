import Hypernets.Graph.RecursiveIsoPlug
import Hypernets.Graph.DeepInventoryExamples

/-! Independent renaming inside boxes strictly extends literal-label isomorphism. -/
namespace Hypernets.Linear.Examples
open Graph

/-- Exchange the names of the two edges while leaving their incidence roles unchanged. -/
def swapTwo : Bijection (Fin 2) (Fin 2) where
  toFun i := ⟨1 - i.val, by omega⟩
  invFun i := ⟨1 - i.val, by omega⟩
  left_inv i := by apply Fin.ext; dsimp; omega
  right_inv i := by apply Fin.ext; dsimp; omega

@[reducible] def renamedTwoHoles : Hypernet operations 0 [.term] [.term] :=
  twoHoles.reindex (Bijection.refl _) swapTwo

def twoHoles_deepIso : DeepIso twoHoles renamedTwoHoles :=
  DeepIso.ofIso (twoHoles.reindexIso (Bijection.refl _) swapTwo)

/-- The records differ: the edge named zero carries different hole labels. -/
theorem renamedTwoHoles_ne : twoHoles ≠ renamedTwoHoles := by
  intro eq
  have labels : HEq twoHoles.edgeLabel renamedTwoHoles.edgeLabel := by rw [eq]
  have atZero := congrFun (eq_of_heq labels) (0 : Fin 2)
  have names := congrArg (fun x : (alphabet operations 0).Symbol =>
    (primitiveHole x.down).map Hole.name) atZero
  change some 0 = some 1 at names
  cases names

@[reducible] def renamedBoxedTwoHoles : Hypernet operations 1 [.thunk 0] [.term] :=
  box (bound := 0) (free := 1) renamedTwoHoles

/-- The bodies may have different records and still define equivalent boxes. -/
def boxedTwoHoles_deepIso : DeepIso boxedTwoHoles renamedBoxedTwoHoles :=
  DeepIso.box (bound := 0) (free := 1) twoHoles_deepIso

/-- Literal label preservation cannot relate these boxes: their labels contain
unequal body records. Recursive isomorphism identifies strictly more graphs. -/
theorem boxedTwoHoles_no_literalIso : ¬ Nonempty (Net.Iso boxedTwoHoles renamedBoxedTwoHoles) := by
  rintro ⟨f⟩
  have labels := f.edge_label (0 : Fin 1)
  change Sum.inr (⟨0, 1, renamedTwoHoles⟩ : Box (alphabet operations 0)) =
    (Sum.inr (⟨0, 1, twoHoles⟩ : Box (alphabet operations 0)) : Primitive Op ⊕ _) at labels
  have bodies : renamedTwoHoles = twoHoles := eq_of_heq (Box.mk.inj (Sum.inr.inj labels)).2.2
  exact renamedTwoHoles_ne bodies.symm

theorem renamedBoxedTwoHoles_unique : UniqueHoles operations 1 renamedBoxedTwoHoles :=
  (DeepIso.uniqueHoles_iff boxedTwoHoles_deepIso).mp boxedTwoHoles_unique

/-- The quotient identifies these different boxed representatives. -/
theorem renamedBoxes_same_class :
    Quotient.mk (deepSetoid operations 1 [.thunk 0] [.term]) boxedTwoHoles =
      Quotient.mk (deepSetoid operations 1 [.thunk 0] [.term]) renamedBoxedTwoHoles :=
  Quotient.sound ⟨boxedTwoHoles_deepIso⟩

/-- A nontrivial address inside a box respects replacement renaming. -/
noncomputable def deep_plug_renaming :
    DeepIso (plugAt boxedFirstSite twoHoles) (plugAt boxedFirstSite renamedTwoHoles) :=
  plugAt_deepIso boxedFirstSite twoHoles_deepIso

/-- Changing an actual primitive operation is not a permitted renaming. -/
theorem distinct_operations_not_equivalent :
    ¬ LabelEquiv operations 0 (ULift.up (.operation Op.value)) (ULift.up (.operation Op.otherValue)) := by
  intro eq
  cases eq

end Hypernets.Linear.Examples

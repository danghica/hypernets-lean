import Hypernets.Copying.AtomicEmbeddingBoundary
import Hypernets.Copying.WeakeningEdgeOccurrence

/-! Compositional exhaustive complements containing one genuine weakening.
These certificates retain the complete old graph and have no semantic premises. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph Opening

structure Complement {d I O J K} (s : ShareSort) (G : Hypernet d I O) (H : Hypernet d J K) where
  old : Occurrence G H
  added : Occurrence (primitiveNet d (.weakening s)) H
  disjoint : ∀ e a, old.edges e ≠ added.edges a
  cover : ∀ e, (∃ a, old.edges a = e) ∨ ∃ b, added.edges b = e

namespace Complement
variable {d I O J K s} {G : Hypernet d I O} {H : Hypernet d J K} (q : Complement s G H)

noncomputable def tensorRight {U V} (X : Hypernet d U V) :
    Complement s (Net.Tensor.net G X) (Net.Tensor.net H X) where
  old := q.old.tensorMap (Occurrence.ofIso (DeepIso.refl X))
  added := q.added.comp (Occurrence.tensorComponent H X false)
  disjoint := by
    cases d <;> rintro ⟨b,e⟩ a eq <;> cases b
    all_goals first
      | exact q.disjoint e a (eq_of_heq (Sigma.mk.inj eq).2)
      | cases eq
  cover := by
    cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first
      | exact .inl ⟨⟨true,e⟩,rfl⟩
      | (rcases q.cover e with ⟨a,eq⟩ | ⟨a,eq⟩
         · exact .inl ⟨⟨false,a⟩,congrArg (Sigma.mk false) eq⟩
         · exact .inr ⟨a,congrArg (Sigma.mk false) eq⟩)

noncomputable def tensorLeft {U V} (X : Hypernet d U V) :
    Complement s (Net.Tensor.net X G) (Net.Tensor.net X H) where
  old := (Occurrence.ofIso (DeepIso.refl X)).tensorMap q.old
  added := q.added.comp (Occurrence.tensorComponent X H true)
  disjoint := by
    cases d <;> rintro ⟨b,e⟩ a eq <;> cases b
    all_goals first
      | exact q.disjoint e a (eq_of_heq (Sigma.mk.inj eq).2)
      | cases eq
  cover := by
    cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first
      | exact .inl ⟨⟨false,e⟩,rfl⟩
      | (rcases q.cover e with ⟨a,eq⟩ | ⟨a,eq⟩
         · exact .inl ⟨⟨true,a⟩,congrArg (Sigma.mk true) eq⟩
         · exact .inr ⟨a,congrArg (Sigma.mk true) eq⟩)

noncomputable def castInterfaces {U V W X} (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) :
    Complement s (Translation.castInterfaces hi ho G) (Translation.castInterfaces hj hk H) := by
  cases hi; cases ho; cases hj; cases hk
  exact q

theorem castInterfaces_old {U V W X} (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X) :
    (q.castInterfaces hi ho hj hk).old = q.old.castInterfaces hi ho hj hk := by
  cases hi; cases ho; cases hj; cases hk; rfl

theorem castInterfaces_added_output {U V W X} (hi : I = U) (ho : O = V) (hj : J = W) (hk : K = X)
    (a : Fin 1) (b : Fin K.length) (eq : q.added.ports (.output a) = .output b) :
    (q.castInterfaces hi ho hj hk).added.ports (.output a) = .output (Fin.cast (congrArg List.length hk) b) := by
  cases hi; cases ho; cases hj; cases hk; exact eq

end Complement

noncomputable def Complement.serialPrefix {d I J O K s} {G : Hypernet d J O} {H : Hypernet d J K}
    (q : Complement s G H) (P : Hypernet d I J)
    (inputs : ∀ i, q.old.ports (.input i) = .input i) :
    Complement s (Serial.net P G) (Serial.net P H) where
  old := q.old.serialPrefix P inputs
  added := q.added.comp (Occurrence.serialRight P H)
  disjoint := by
    cases d <;> rintro ⟨b,e⟩ a eq <;> cases b
    all_goals first | cases eq | exact q.disjoint e a (eq_of_heq (Sigma.mk.inj eq).2)
  cover := by
    cases d <;> rintro ⟨b,e⟩ <;> cases b
    all_goals first
      | exact .inl ⟨⟨false,e⟩,rfl⟩
      | (rcases q.cover e with ⟨a,eq⟩ | ⟨a,eq⟩
         · exact .inl ⟨⟨true,a⟩,congrArg (Sigma.mk true) eq⟩
         · exact .inr ⟨a,congrArg (Sigma.mk true) eq⟩)

/-- Ordered boundary laws turn the exhaustive complement into the required
outside-weakening isomorphism, rather than an assumed equivalence. -/
noncomputable def Complement.extensionIso {d I k h s}
    {G : Hypernet d I (environmentInterface k h)}
    {H : Hypernet d I (environmentInterface (BoxPullWeakening.variables s k) (BoxPullWeakening.atoms s h))}
    (q : Complement s G H)
    (inputs : ∀ i, q.old.ports (.input i) = .input i)
    (outputs : ∀ i, q.old.ports (.output i) = .output (BoxPullWeakening.RetainedCopy.outputIndex s i))
    (added : ∀ i, q.added.ports (.output i) = .output (BoxPullWeakening.CopyRow.addedOutput k h s)) :
    DeepIso (BoxPullWeakening.extend G s) H :=
  Extension.iso {
    old := q.old
    added := q.added
    disjoint := q.disjoint
    cover := q.cover
    input := inputs
    output := outputs
    new_output := added }
theorem Complement.tensorRight_added_output {d I O J K U V s}
    {G : Hypernet d I O} {H : Hypernet d J K} (q : Complement s G H) (X : Hypernet d U V)
    (a : Fin 1) (b : Fin K.length) (eq : q.added.ports (.output a) = .output b) :
    (q.tensorRight X).added.ports (.output a) = .output (Net.Tensor.join K V ⟨false,b⟩) := by
  change (Occurrence.tensorComponent H X false).ports (q.added.ports (.output a)) = _
  rw [eq]
  rfl

theorem Complement.tensorLeft_added_output {d I O J K U V s}
    {G : Hypernet d I O} {H : Hypernet d J K} (q : Complement s G H) (X : Hypernet d U V)
    (a : Fin 1) (b : Fin K.length) (eq : q.added.ports (.output a) = .output b) :
    (q.tensorLeft X).added.ports (.output a) = .output (Net.Tensor.join V K ⟨true,b⟩) := by
  change (Occurrence.tensorComponent X H true).ports (q.added.ports (.output a)) = _
  rw [eq]
  rfl

theorem Complement.serialPrefix_added_output {d I J O K s}
    {G : Hypernet d J O} {H : Hypernet d J K} (q : Complement s G H) (P : Hypernet d I J)
    (inputs : ∀ i, q.old.ports (.input i) = .input i)
    (a : Fin 1) (b : Fin K.length) (eq : q.added.ports (.output a) = .output b) :
    (q.serialPrefix P inputs).added.ports (.output a) = .output b := by
  change BoundarySerial.rightInsert P H (q.added.ports (.output a)) = _
  rw [eq,Application.right_serial_output]

end Hypernets.Copying.Weakening

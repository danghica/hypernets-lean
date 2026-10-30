import Hypernets.Copying.CopyFrames
import Hypernets.Copying.SharingTreeExpansion

/-! The residual sharing component of the original copying rule is itself a
finite contraction tree. Its selected input is fed by the actual weakening. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph
variable {n} (T : ContractionTree .term (n+1))

theorem residualFrame_acyclic : ∀ {es}, (residualFrame n).Path es → es.Nodup :=
  Net.path_nodup_of_rank (residualFrame n) (fun (b : Bool) => if b then 1 else 0)
    (by
      rintro a b ⟨v,target,source⟩
      cases a <;> cases b <;> simp_all [residualFrame,residualSource,residualTarget])

/-- Feeding the selected input with weakening leaves every remaining input
in its original order and preserves genuine tree acyclicity. -/
def residualTree : ContractionTree .term n where
  net := (residualFrame n).expand (residualFill T)
  labels e := by
    rcases e with ⟨b,e⟩
    cases b
    · exact .inl rfl
    · exact T.labels e
  acyclic := by
    apply SharingTreeExpansion.acyclic_expand (residualFrame n) (residualFill T)
      (residualFrame_acyclic (n := n))
    · intro b; cases b <;> rfl
    · intro b es path
      cases b
      · exact Net.path_nodup_of_rank (residualFill T false) (fun _ => 0)
          (by rintro e f ⟨v,target,source⟩; simp [residualFill,residualLabel,Net.corolla,primitiveSignature] at source) path
      · exact T.acyclic path
    · intro b e
      cases b
      · rfl
      · exact T.target_single e

theorem residualTree_atDepth (d : Nat) : (residualTree T).atDepth d = residual T d := rfl

end Hypernets.Copying.CopyRule

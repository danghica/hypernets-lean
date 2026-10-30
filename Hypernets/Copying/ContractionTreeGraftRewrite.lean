import Hypernets.Copying.ContractionTreeGraftSerial
import Hypernets.Copying.ContractionTreeGraftWitness
import Hypernets.Copying.CombinedRules

/-! Actual rewrites of the selected downstream component of a graft.
All unselected inputs retain their literal external ordering. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph Combined

/-- An original downstream rewrite lifts through the literal partial serial
context; no copying transition is replaced by a derived compute rule. -/
theorem rewrite_right {s : ShareSort} {a b d O}
    (P : Hypernet d (List.replicate a s.wire) [s.wire])
    {G H : Hypernet d (List.replicate (b+1) s.wire) O}
    (j : Fin (b+1)) {v w} (step : Rewrite G v H w) :
    Rewrite (net P G j) (rightInsert P G j v)
      (net P H j) (rightInsert P H j w) := by
  cases d
  all_goals
    apply Rewrite.expand (pattern s a b O j _) (filling P G j) (filling P H j) true
    · intro e ne
      cases e
      · rfl
      · exact (ne rfl).elim
    · exact step

/-- When the attached downstream input is positive, downstream input zero
remains external, immediately after the upstream inputs. -/
theorem right_zero {s : ShareSort} {a b d O}
    (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) O)
    (j : Fin (b+1)) (positive : 0 < j.val) :
    rightInsert P G j (.input ⟨0,by simp⟩) =
      .input ⟨a,by simp; omega⟩ := by
  rw [right_input]
  simp only [downstream]
  have ne : (⟨0,by omega⟩ : Fin (b+1)) ≠ j := by intro eq; have val : 0 = j.val := congrArg Fin.val eq; omega
  simp only [ne,↓reduceDIte,positive,↓reduceIte,Nat.add_zero,Port.map]

/-- An equality of ordered input interfaces commutes with an unchanged
serial continuation. This transport has no input permutation. -/
def serial_input {d I J K O} (G : Hypernet d I J) (H : Hypernet d J O)
    (hi : I = K) :
    DeepIso (Serial.net (G.reboundary hi rfl) H)
      ((Serial.net G H).reboundary hi rfl) := by
  cases hi
  simpa only [Net.reboundary_refl] using DeepIso.refl (Serial.net G H)

/-- The copying source for the full graft is the literal original downstream
copying source in the graft context, with only its explicit arity equality. -/
noncomputable def copy_source_iso {d m b k h}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (b+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (j : Fin (b+1)) :
    DeepIso (CopyRule.before (copyTree P T j) H)
      ((net (P.atDepth d) (CopyRule.before T H) j).reboundary (by congr 1; omega) rfl) := by
  have first := Serial.congr (copyTree_iso P T j d) (DeepIso.refl H)
  have second := serial_input (net (P.atDepth d) (T.atDepth d) j) H
    (show List.replicate ((m+1)+b) Wire.term = List.replicate (m+b+1) Wire.term by congr 1; omega)
  have third := CopyRule.reboundaryIso (SerialRight.iso (P.atDepth d) (T.atDepth d) H j).symm
    (show List.replicate ((m+1)+b) Wire.term = List.replicate (m+b+1) Wire.term by congr 1; omega) rfl
  exact first.trans (second.trans third)

end Hypernets.Copying.ContractionTree.Graft

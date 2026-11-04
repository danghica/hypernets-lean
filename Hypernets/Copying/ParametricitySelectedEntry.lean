import Hypernets.Copying.ParametricityFamilyLiteral
import Hypernets.Copying.ParametricityTemplate
import Hypernets.Copying.BoundaryOccurrence

/-! Every original family input exposes a complete original lambda payload,
including its full recursive box body. Both sides select the same kind of
member at the same external input; this is stronger than head recognition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Opening

/-- The two possible complete corresponding payloads at an actual input.
This records occurrences only; it adds no constructor to the template pair. -/
inductive SelectedEntry : {d : Nat} → {I O : List Wire} →
    Hypernet d I O → Hypernet d I O → Fin I.length → Prop where
  | large {d I O} {G H : Hypernet (d+2) I O} {i : Fin I.length}
      (left : Occurrence (largeLeft d) G) (right : Occurrence (largeRight d) H)
      (leftInput : left.ports (.input 0) = .input i)
      (rightInput : right.ports (.input 0) = .input i) : SelectedEntry G H i
  | small {d I O} {G H : Hypernet (d+2) I O} {i : Fin I.length}
      (left : Occurrence (smallLeft (d+1)) G) (right : Occurrence (smallRight (d+1)) H)
      (leftInput : left.ports (.input 0) = .input i)
      (rightInput : right.ports (.input 0) = .input i) : SelectedEntry G H i

/-- Independent whole-graph carrier changes fix the selected input and
preserve complete payload incidences and recursive box labels. -/
theorem SelectedEntry.rename {d I O} {G H A B : Hypernet d I O} {i}
    (entry : SelectedEntry G H i) (f : DeepIso G A) (g : DeepIso H B) :
    SelectedEntry A B i := by
  cases entry with
  | large l r li ri =>
    apply SelectedEntry.large (l.comp (Occurrence.ofIso f)) (r.comp (Occurrence.ofIso g))
    · change Port.map f.vertices.toFun (l.ports (.input 0)) = .input i
      rw [li]; rfl
    · change Port.map g.vertices.toFun (r.ports (.input 0)) = .input i
      rw [ri]; rfl
  | small l r li ri =>
    apply SelectedEntry.small (l.comp (Occurrence.ofIso f)) (r.comp (Occurrence.ofIso g))
    · change Port.map f.vertices.toFun (l.ports (.input 0)) = .input i
      rw [li]; rfl
    · change Port.map g.vertices.toFun (r.ports (.input 0)) = .input i
      rw [ri]; rfl

namespace MemberOccurrence
variable (d m n : Nat) (C : ContractionTree .term (m+n))

noncomputable def largeLeftFamily (i : Fin m) : Occurrence (largeLeft d) (leftFamily d m n) :=
  (FamilyComponents.large (k := 1) (largeLeft d) (smallLeft (d+1)) m n i).comp
    (FamilyLiteral.leftOccurrence d m n)
noncomputable def largeRightFamily (i : Fin m) : Occurrence (largeRight d) (rightFamily d m n) :=
  (FamilyComponents.large (k := 0) (largeRight d) (smallRight (d+1)) m n i).comp
    (FamilyLiteral.rightOccurrence d m n)
noncomputable def smallLeftFamily (i : Fin n) : Occurrence (smallLeft (d+1)) (leftFamily d m n) :=
  (FamilyComponents.small (k := 1) (largeLeft d) (smallLeft (d+1)) m n i).comp
    (FamilyLiteral.leftOccurrence d m n)
noncomputable def smallRightFamily (i : Fin n) : Occurrence (smallRight (d+1)) (rightFamily d m n) :=
  (FamilyComponents.small (k := 0) (largeRight d) (smallRight (d+1)) m n i).comp
    (FamilyLiteral.rightOccurrence d m n)

theorem largeLeftFamily_input (i : Fin m) :
    (largeLeftFamily d m n i).ports (.input 0) = .input ⟨i.val,by simp;omega⟩ := by
  change (FamilyLiteral.leftOccurrence d m n).ports
    ((FamilyComponents.large (k := 1) (largeLeft d) (smallLeft (d+1)) m n i).ports (.input 0)) = _
  rw [FamilyComponents.large_input]
  rfl
theorem largeRightFamily_input (i : Fin m) :
    (largeRightFamily d m n i).ports (.input 0) = .input ⟨i.val,by simp;omega⟩ := by
  change (FamilyLiteral.rightOccurrence d m n).ports
    ((FamilyComponents.large (k := 0) (largeRight d) (smallRight (d+1)) m n i).ports (.input 0)) = _
  rw [FamilyComponents.large_input]
  rfl
theorem smallLeftFamily_input (i : Fin n) :
    (smallLeftFamily d m n i).ports (.input 0) = .input ⟨m+i.val,by simp⟩ := by
  change (FamilyLiteral.leftOccurrence d m n).ports
    ((FamilyComponents.small (k := 1) (largeLeft d) (smallLeft (d+1)) m n i).ports (.input 0)) = _
  rw [FamilyComponents.small_input]
  rfl
theorem smallRightFamily_input (i : Fin n) :
    (smallRightFamily d m n i).ports (.input 0) = .input ⟨m+i.val,by simp⟩ := by
  change (FamilyLiteral.rightOccurrence d m n).ports
    ((FamilyComponents.small (k := 0) (largeRight d) (smallRight (d+1)) m n i).ports (.input 0)) = _
  rw [FamilyComponents.small_input]
  rfl

/-- The whole family occurs beneath its unchanged original tree and cell. -/
noncomputable def privateFamily : Occurrence (leftFamily d m n) (left d C) :=
  (BoxPullWeakening.ReverseComponents.serialLeft (leftFamily d m n) (C.atDepth (d+2))).comp
    (BoxPullWeakening.ReverseComponents.serialLeft
      (Serial.net (leftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2)))

theorem privateFamily_input (i : Fin (List.replicate (m+n) Wire.term).length) :
    (privateFamily d m n C).ports (.input i) = .input i := by
  change BoundarySerial.leftInsert
    (Serial.net (leftFamily d m n) (C.atDepth (d+2))) (privateCell (d+2))
      (BoundarySerial.leftInsert (leftFamily d m n) (C.atDepth (d+2)) (.input i)) = _
  rw [Combined.left_input,Combined.left_input]

end MemberOccurrence

/-- At every original ordered input, the full corresponding large or small
abstraction occurs on both sides, including all of its original box body. -/
theorem Literal.selected_entry {d I O} {G H : Hypernet d I O}
    (pair : Literal G H) (i : Fin I.length) : SelectedEntry G H i := by
  cases pair with
  | @families m n d C =>
    have bound : i.val < m+n := by simpa using i.isLt
    by_cases large : i.val < m
    · let j : Fin m := ⟨i.val,large⟩
      apply SelectedEntry.large
        ((MemberOccurrence.largeLeftFamily d m n j).comp (MemberOccurrence.privateFamily d m n C))
        (MemberOccurrence.largeRightFamily d m n j)
      · change (MemberOccurrence.privateFamily d m n C).ports
          ((MemberOccurrence.largeLeftFamily d m n j).ports (.input 0)) = _
        rw [MemberOccurrence.largeLeftFamily_input,MemberOccurrence.privateFamily_input]
      · exact MemberOccurrence.largeRightFamily_input d m n j
    · let j : Fin n := ⟨i.val-m,by omega⟩
      have index : (⟨m+j.val,by simp⟩ : Fin (List.replicate (m+n) Wire.term).length) = i :=
        Fin.ext (by dsimp [j];omega)
      apply SelectedEntry.small
        ((MemberOccurrence.smallLeftFamily d m n j).comp (MemberOccurrence.privateFamily d m n C))
        (MemberOccurrence.smallRightFamily d m n j)
      · change (MemberOccurrence.privateFamily d m n C).ports
          ((MemberOccurrence.smallLeftFamily d m n j).ports (.input 0)) = _
        rw [MemberOccurrence.smallLeftFamily_input,MemberOccurrence.privateFamily_input,index]
      · rw [MemberOccurrence.smallRightFamily_input,index]

/-- The complete input-payload classification holds for independently
represented original parametricity pairs, with no matching or semantic premise. -/
theorem Pair.selected_entry {d I O} {G H : Hypernet d I O}
    (pair : Pair G H) (i : Fin I.length) : SelectedEntry G H i := by
  cases pair with
  | witness f literal g => exact (literal.selected_entry i).rename f.symm g

end Hypernets.Copying.Parametricity

namespace Hypernets.Copying.CopyRule.NormalForm
open Graph Opening

/-- Two complete normalized payload occurrences at the same incoming wire
have the same full recursive graph class, including all interface metadata.
Head uniqueness supplies the edge equality required by payload rigidity. -/
theorem related_inputs {d k h l j I O}
    {A : Hypernet d [.term] (environmentInterface k h)}
    {B : Hypernet d [.term] (environmentInterface l j)} {G : Hypernet d I O}
    (a : NormalForm A) (b : NormalForm B) (f : Occurrence A G) (g : Occurrence B G)
    (input : f.ports (.input 0) = g.ports (.input 0)) : PayloadRelated A B := by
  have left := f.matchEmbedding.head a.head_at
  have right := g.matchEmbedding.head b.head_at
  change MatchEmbedding.HeadAt G (f.ports (.input 0)) (f.edges a.head) a.primitive at left
  change MatchEmbedding.HeadAt G (g.ports (.input 0)) (g.edges b.head) b.primitive at right
  rw [input] at left
  exact (related a b f g (MatchEmbedding.head_unique left right).1).1

end Hypernets.Copying.CopyRule.NormalForm

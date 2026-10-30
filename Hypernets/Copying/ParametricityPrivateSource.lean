import Hypernets.Copying.ParametricitySmallFamilyRead

/-! The entire original private term tree and allocated cell form one
complete occurrence beneath the active reader. Every other term input and
the literal canonical atom distributor remain present. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.PrivateSource
open Graph Opening Combined
variable {n} (T : ContractionTree .term (n+1)) (d : Nat)

abbrev value := primitiveNet d .instanceEdge
abbrev payload := CopyRule.before (k := 0) (h := 1) T (value d)

noncomputable def prefixOccurrence : Occurrence (ReaderPrefix.net (payload T d)) (PrivateRead.before T d) :=
  BoxPullWeakening.ReverseComponents.serialLeft _ _
noncomputable def tail : Occurrence (PrivateRead.tail d) (PrivateRead.before T d) :=
  BoxPullWeakening.ReverseComponents.serialRight _ _
noncomputable def contents : Occurrence (payload T d) (PrivateRead.before T d) := by
  cases d
  all_goals exact (Occurrence.expand (ReaderPrefix.pattern _ n (environmentInterface 0 1))
    (ReaderPrefix.filling (payload T _)) true).comp (prefixOccurrence T _)

theorem linked (i : Fin [Wire.atom].length) :
    (contents T d).ports (.output i) = (tail T d).ports (.input i) := by
  change Fin 1 at i
  have zero : i = 0 := Subsingleton.elim _ _
  subst i
  cases d <;> rfl

theorem apart : ∀ e a, (contents T d).edges e ≠ (tail T d).edges a := by
  cases d <;> intro e a eq <;> cases eq

noncomputable def combined : Occurrence (Serial.net (payload T d) (PrivateRead.tail d)) (PrivateRead.before T d) :=
  Occurrence.SerialJoin.occurrence (contents T d) (tail T d) (linked T d) (apart T d)

/-- Recover the original cell's exact association of instance, atom D1,1,
store, and numeral, retaining all four genuine components. -/
noncomputable def cell_prefix : DeepIso (privateCell d) (Serial.net (value d) (PrivateRead.tail d)) :=
  (PrivateRead.cell_association d).trans
    (Serial.congr (DeepIso.refl _)
      (Serial.Association.iso (CanonicalTree.atDepth .atom 1 d)
        (primitiveNet d .store) (ReadTail.numeral d)).symm)

noncomputable def source_iso : DeepIso (Serial.net (T.atDepth d) (privateCell d))
    (Serial.net (payload T d) (PrivateRead.tail d)) :=
  (Serial.congr (DeepIso.refl _) (cell_prefix d)).trans
    (Serial.Association.iso (T.atDepth d) (value d) (PrivateRead.tail d)).symm

noncomputable def occurrence : Occurrence (Serial.net (T.atDepth d) (privateCell d)) (PrivateRead.before T d) :=
  (Occurrence.ofIso (source_iso T d)).comp (combined T d)

/-- The complete private component attaches to the actual reader output. -/
theorem selected_input : (occurrence T d).ports (.input ⟨0,by simp⟩) =
    BoundarySerial.leftInsert (ReaderPrefix.net (payload T d)) (PrivateRead.tail d)
      (ReaderPrefix.active (payload T d)) := by
  change (combined T d).ports (Port.map (source_iso T d).vertices.toFun (.input ⟨0,by simp⟩)) = _
  change (combined T d).ports (.input ⟨0,by simp⟩) = _
  rw [combined,Occurrence.SerialJoin.occurrence_input]
  cases d <;> rfl

theorem remaining_input (i : Fin n) : (occurrence T d).ports (.input ⟨i.val+1,by simp⟩) =
    .input ⟨i.val+1,by simp⟩ := by
  change (combined T d).ports (Port.map (source_iso T d).vertices.toFun (.input ⟨i.val+1,by simp⟩)) = _
  change (combined T d).ports (.input ⟨i.val+1,by simp⟩) = _
  rw [combined,Occurrence.SerialJoin.occurrence_input]
  cases d with
  | zero =>
    change BoundarySerial.leftInsert (ReaderPrefix.net (payload T 0)) (PrivateRead.tail 0)
      (Port.map Sum.inl ((ReaderPrefix.pattern 0 n (environmentInterface 0 1)).sourcePort true _)) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,Net.relabel,ReaderPrefix.frame,ReaderPrefix.source,
      List.getElem_cons_succ,List.getElem_map,List.getElem_finRange,Port.map,Fin.val_cast]
    exact left_input _ _ _
  | succ k =>
    change BoundarySerial.leftInsert (ReaderPrefix.net (payload T (k+1))) (PrivateRead.tail (k+1))
      (Port.map Sum.inl ((ReaderPrefix.pattern (k+1) n (environmentInterface 0 1)).sourcePort true _)) = _
    simp only [Net.sourcePort,ReaderPrefix.pattern,Net.relabel,ReaderPrefix.frame,ReaderPrefix.source,
      List.getElem_cons_succ,List.getElem_map,List.getElem_finRange,Port.map,Fin.val_cast]
    exact left_input _ _ _


def readerEdge : (PrivateRead.before T d).Edge := by
  cases d <;> exact ⟨false,⟨false,(0 : Fin 1)⟩⟩

theorem covers_contents (e : (payload T d).Edge) :
    ∃ a, (occurrence T d).edges a = (contents T d).edges e := by
  cases d with
  | zero => exact ⟨(source_iso T 0).edges.invFun ⟨false,e⟩,
      congrArg (combined T 0).edges ((source_iso T 0).edges.right_inv ⟨false,e⟩)⟩
  | succ k => exact ⟨(source_iso T (k+1)).edges.invFun ⟨false,e⟩,
      congrArg (combined T (k+1)).edges ((source_iso T (k+1)).edges.right_inv ⟨false,e⟩)⟩

theorem covers_tail (e : (PrivateRead.tail d).Edge) :
    ∃ a, (occurrence T d).edges a = (tail T d).edges e := by
  cases d with
  | zero => exact ⟨(source_iso T 0).edges.invFun ⟨true,e⟩,
      congrArg (combined T 0).edges ((source_iso T 0).edges.right_inv ⟨true,e⟩)⟩
  | succ k => exact ⟨(source_iso T (k+1)).edges.invFun ⟨true,e⟩,
      congrArg (combined T (k+1)).edges ((source_iso T (k+1)).edges.right_inv ⟨true,e⟩)⟩

/-- The complete original private component accounts for every edge except
the one active dereference itself. No tree sibling or cell edge is omitted. -/
theorem cover (e : (PrivateRead.before T d).Edge) :
    e = readerEdge T d ∨ ∃ a, (occurrence T d).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨part,e⟩
    cases part
    · rcases e with ⟨part,e⟩
      cases part
      · change Fin 1 at e
        have zero : e = (0 : Fin 1) := Subsingleton.elim _ _
        subst e
        exact .inl rfl
      · exact .inr (covers_contents T _ e)
    · exact .inr (covers_tail T _ e)

end Hypernets.Copying.Parametricity.PrivateSource

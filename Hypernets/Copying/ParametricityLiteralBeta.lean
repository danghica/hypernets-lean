import Hypernets.Copying.ParametricityDiagramBoundary
import Hypernets.Copying.ParametricitySmallReadDiagram
import Hypernets.Copying.ParametricityLargeBareDiagram
import Hypernets.Copying.ParametricityCopyPresentation
import Hypernets.Copying.ParametricityBareApplyCanonical

/-! The checked bare application diagrams at every original Figure20 family
member. The selected source retains the exact supplied private tree, and
all changes of boundary order act synchronously on the two sides. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LiteralBeta
open Graph Combined

/-- A large member has no post-opening steps: both original beta targets
are related by the independently constructed remaining-family specimen. -/
noncomputable def largeCanonical {m n} (d : Nat)
    (C : ContractionTree .term ((m+n)+1)) :
    ReadDiagram (BareApplyFirst.net (LargeBareSource.closedGraph d C)) (.input ⟨0,by simp⟩)
      (BareApplyFirst.net (IsolatedFamily.largeRightFamily d m n)) (.input ⟨0,by simp⟩) 0 :=
  ReadDiagram.of_pointed (LargeBareDiagram.leftOpening d C)
    (LargeBareDiagram.rightOpening (m := m) (n := n) d)
    (LargeBareDiagram.residual d C) (by
      change (List.replicate ((m+n)+1) Wire.term)[0] = .term
      simp)

private theorem targetCast_inputs {d I O J K U V}
    {G : Hypernet d I O} {H : Hypernet d J K} (f : BoundaryIso G H)
    (hi : J=U) (ho : K=V) (i : Fin I.length) :
    (f.trans (BoundaryIso.interfaceEquality H hi ho)).inputs.toFun i =
      Fin.cast (congrArg List.length hi) (f.inputs.toFun i) := by
  apply Port.input.inj (Internal := (H.reboundary hi ho).Internal) (outputs := V.length)
  dsimp only [BoundaryIso.inputs]
  rw [← BoundaryIso.map_input]
  change (BoundaryIso.interfaceEquality H hi ho).ports.toFun (f.ports.toFun (.input i)) = _
  rw [f.map_input,BoundaryIso.interfaceEquality_port]
  rfl

/-- The actual arbitrary private tree can be presented after the isolated
family without changing any original external input coordinate. -/
private theorem isolatedPresentation {d m n b}
    (count : b+1=m+n)
    {L : Hypernet (d+2) (List.replicate (b+1) .term) (List.replicate (b+1) .term)}
    (f : BoundaryIso L (leftFamily d m n)) (C : ContractionTree .term (m+n)) :
    ∃ D : ContractionTree .term (b+1),
      ∃ g : BoundaryIso (Serial.net L (Serial.net (D.atDepth (d+2)) (privateCell (d+2)))) (left d C),
        ∀ i,g.inputs.toFun i=f.inputs.toFun i := by
  obtain ⟨D,g,inputs⟩ := PrivateReindex.presentation count f C
  refine ⟨D,(BoundaryIso.ofDeepIso (Serial.Association.iso L (D.atDepth (d+2)) (privateCell (d+2))).symm).trans g,?_⟩
  intro i
  rw [BoundaryIso.trans_inputs]
  exact inputs i

private theorem transfer {d b steps}
    {L R G H : Hypernet (d+1) (List.replicate (b+1) .term) []}
    (f : BoundaryIso L G) (g : BoundaryIso R H)
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i)
    (j : Fin (b+1)) (selected : BareApplyAt.Boundary.image f 0=j)
    (q : ReadDiagram (BareApplyFirst.net L) (.input ⟨0,by simp⟩)
      (BareApplyFirst.net R) (.input ⟨0,by simp⟩) steps) :
    Nonempty (ReadDiagram (BareApplyAt.net G j) (.input ⟨0,by simp⟩)
      (BareApplyAt.net H j) (.input ⟨0,by simp⟩) steps) := by
  have chosenRight : BareApplyAt.Boundary.image g 0=j :=
    (BareApplyAt.Boundary.image_congr f g same 0).symm.trans selected
  let p := BoundaryWitness.termOrder (BareApplyAt.Boundary.canonical f).inputs
  have result := q.synchronousBoundary (BareApplyAt.Boundary.canonical f)
    (BareApplyAt.Boundary.canonical g) p (fun _ => rfl)
    (fun i => (BareApplyAt.Boundary.canonical_same_inputs f g same i).symm)
    (BareApplyAt.Boundary.canonical_output f) (BareApplyAt.Boundary.canonical_output g)
  change ReadDiagram _ (.input ((BareApplyAt.Boundary.canonical f).inputs.toFun ⟨0,by simp⟩))
    _ (.input ((BareApplyAt.Boundary.canonical f).inputs.toFun ⟨0,by simp⟩)) steps at result
  rw [BareApplyAt.Boundary.canonical_active,selected,chosenRight] at result
  exact ⟨result⟩

/-- Every originally selected large member has a genuine one-versus-one
opening diagram, with its entire original private tree and remaining family. -/
theorem large (d m n : Nat) (C : ContractionTree .term ((m+1)+n))
    (selected : Fin (m+1)) :
    Nonempty (ReadDiagram
      (BareApplyAt.net (n := m+n) ((left d C).reboundary (by congr 1 <;> omega) rfl)
        ⟨selected.val,by have:=selected.isLt;omega⟩) (.input ⟨0,by simp⟩)
      (BareApplyAt.net (n := m+n) ((right d (m+1) n).reboundary (by congr 1 <;> omega) rfl)
        ⟨selected.val,by have:=selected.isLt;omega⟩) (.input ⟨0,by simp⟩) 0) := by
  let f := IsolatedFamily.largeLeftAtIso d m n selected
  let g := IsolatedFamily.largeRightAtIso d m n selected
  obtain ⟨D,l,inputs⟩ := isolatedPresentation (by omega : (m+n)+1=(m+1)+n) f C
  have same : ∀ i,l.inputs.toFun i=g.inputs.toFun i :=
    fun i => (inputs i).trans (IsolatedFamily.largeAt_same_inputs d m n selected i)
  let hi : List.replicate ((m+1)+n) Wire.term=List.replicate ((m+n)+1) Wire.term := by congr 1 <;> omega
  let li := l.trans (BoundaryIso.interfaceEquality (left d C) hi rfl)
  let ri := g.trans (BoundaryIso.interfaceEquality (right d (m+1) n) hi rfl)
  have synchronized : ∀ i,li.inputs.toFun i=ri.inputs.toFun i := by
    intro i
    exact (targetCast_inputs l hi rfl i).trans
      ((congrArg (Fin.cast (congrArg List.length hi)) (same i)).trans
        (targetCast_inputs g hi rfl i).symm)
  apply transfer li ri synchronized ⟨selected.val,by have:=selected.isLt;omega⟩ _ (largeCanonical d D)
  apply Fin.ext
  change (li.inputs.toFun ⟨0,by simp⟩).val=selected.val
  rw [targetCast_inputs,inputs]
  have first := IsolatedFamily.largeLeftAtIso_first d m n selected
  have picked := Port.input.inj ((f.map_input ⟨0,by simp⟩).symm.trans first)
  exact congrArg Fin.val picked

/-- Every originally selected small member has its actual eight-step read
suffix after beta, followed by the proved structural corrections and the
original remaining-family specimen. -/
theorem small (d m n : Nat) (C : ContractionTree .term (m+(n+1)))
    (selected : Fin (n+1)) :
    Nonempty (ReadDiagram
      (BareApplyAt.net (n := m+n) ((left d C).reboundary (by congr 1 <;> omega) rfl)
        ⟨m+selected.val,by have:=selected.isLt;omega⟩) (.input ⟨0,by simp⟩)
      (BareApplyAt.net (n := m+n) ((right d m (n+1)).reboundary (by congr 1 <;> omega) rfl)
        ⟨m+selected.val,by have:=selected.isLt;omega⟩) (.input ⟨0,by simp⟩) 8) := by
  let f := IsolatedFamily.smallLeftAtIso d m n selected
  let g := IsolatedFamily.smallRightAtIso d m n selected
  obtain ⟨D,l,inputs⟩ := isolatedPresentation (by omega : (m+n)+1=m+(n+1)) f C
  have same : ∀ i,l.inputs.toFun i=g.inputs.toFun i :=
    fun i => (inputs i).trans (IsolatedFamily.smallAt_same_inputs d m n selected i)
  let hi : List.replicate (m+(n+1)) Wire.term=List.replicate ((m+n)+1) Wire.term := by congr 1 <;> omega
  let li := l.trans (BoundaryIso.interfaceEquality (left d C) hi rfl)
  let ri := g.trans (BoundaryIso.interfaceEquality (right d m (n+1)) hi rfl)
  have synchronized : ∀ i,li.inputs.toFun i=ri.inputs.toFun i := by
    intro i
    exact (targetCast_inputs l hi rfl i).trans
      ((congrArg (Fin.cast (congrArg List.length hi)) (same i)).trans
        (targetCast_inputs g hi rfl i).symm)
  obtain ⟨q⟩ := SmallBareDiagram.normalized d D
  apply transfer li ri synchronized ⟨m+selected.val,by have:=selected.isLt;omega⟩ _ q
  apply Fin.ext
  change (li.inputs.toFun ⟨0,by simp⟩).val=m+selected.val
  rw [targetCast_inputs,inputs]
  have first := IsolatedFamily.smallLeftAtIso_first d m n selected
  have picked := Port.input.inj ((f.map_input ⟨0,by simp⟩).symm.trans first)
  exact congrArg Fin.val picked

/-- Every ordered member of the full original literal family admits the
actual beta/read/correction diagram. Either block may be empty; no selected
member, private-tree presentation, or argument-retention premise remains. -/
theorem all_inputs {b} (d m n : Nat) (C : ContractionTree .term (m+n))
    (count : m+n=b+1) (j : Fin (b+1)) :
    ∃ steps,(steps=0 ∨ steps=8) ∧ Nonempty (ReadDiagram
      (BareApplyAt.net ((left d C).reboundary (congrArg (fun n => List.replicate n Wire.term) count) rfl) j)
      (.input ⟨0,by simp⟩)
      (BareApplyAt.net ((right d m n).reboundary (congrArg (fun n => List.replicate n Wire.term) count) rfl) j)
      (.input ⟨0,by simp⟩) steps) := by
  by_cases selected : j.val<m
  · cases m with
    | zero => omega
    | succ m =>
      have arity : b=m+n := by omega
      subst b
      exact ⟨0,Or.inl rfl,large d m n C ⟨j.val,selected⟩⟩
  · cases n with
    | zero => have bound:=j.isLt;omega
    | succ n =>
      have arity : b=m+n := by omega
      subst b
      let i : Fin (n+1) := ⟨j.val-m,by have bound:=j.isLt;omega⟩
      have result := small d m n C i
      have atInput : (⟨m+i.val,by have:=i.isLt;omega⟩ : Fin ((m+n)+1))=j :=
        Fin.ext (by dsimp [i];omega)
      rw [atInput] at result
      exact ⟨8,Or.inr rfl,result⟩

end Hypernets.Copying.Parametricity.LiteralBeta

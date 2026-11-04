import Hypernets.Copying.ParametricityCopyTransport
import Hypernets.Copying.ParametricityIsolatedCopy
import Hypernets.Copying.ParametricityCopyPresentation
import Hypernets.Copying.ContractionTreeGraftBoundary

/-! Copy an arbitrary original Figure20 member through the actual retained
upstream tree. Every boundary permutation is shared by both endpoints and
the exact supplied private tree is recovered by the pulled-back source. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.LiteralCopy
open Graph Combined ContractionTree

/-- Synchronized whole-family boundary changes transport the already proved
copy diagram through a literal graft, fixing the original upstream token. -/
private theorem transfer {d a b} (P : ContractionTree .term (a+1))
    {L R G H : Hypernet d (List.replicate (b+1) .term) []}
    (f : BoundaryIso L G) (g : BoundaryIso R H)
    (same : ∀ i, f.inputs.toFun i = g.inputs.toFun i)
    (j : Fin (b+1)) (selected : Graft.BoundaryRight.image (s := .term) f 0 = j)
    {X Y : Hypernet d (List.replicate ((a+1)+b) .term) []}
    (left : Rewrite (Graft.net (P.atDepth d) L 0) (.input ⟨0,by simp;omega⟩) X (.input ⟨0,by simp;omega⟩))
    (right : Rewrite (Graft.net (P.atDepth d) R 0) (.input ⟨0,by simp;omega⟩) Y (.input ⟨0,by simp;omega⟩))
    (paired : FillingWitness template X Y) :
    ∃ A B : Hypernet d (List.replicate ((a+1)+b) .term) [],
      Rewrite (Graft.net (P.atDepth d) G j) (.input ⟨0,by simp;omega⟩) A (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (P.atDepth d) H j) (.input ⟨0,by simp;omega⟩) B (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  have chosenRight : Graft.BoundaryRight.image (s := .term) g 0 = j :=
    (Graft.BoundaryRight.image_congr (s := .term) f g same 0).symm.trans selected
  have result := CopyTransport.diagram (Graft.BoundaryRight.iso (s := .term) (P.atDepth d) f 0)
    (Graft.BoundaryRight.iso (s := .term) (P.atDepth d) g 0)
    (Graft.BoundaryRight.same_inputs (s := .term) (P.atDepth d) f 0 g same)
    ⟨0,by simp;omega⟩ (Graft.BoundaryRight.active (s := .term) (P.atDepth d) f 0 (by omega)) left right paired
  have ls : Graft.net (P.atDepth d) G (Graft.BoundaryRight.image (s := .term) f 0) =
      Graft.net (P.atDepth d) G j := congrArg (fun j => Graft.net (P.atDepth d) G j) selected
  have rs : Graft.net (P.atDepth d) H (Graft.BoundaryRight.image (s := .term) g 0) =
      Graft.net (P.atDepth d) H j := congrArg (fun j => Graft.net (P.atDepth d) H j) chosenRight
  rw [ls,rs] at result
  exact result

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

/-- Copying any originally selected large member has genuine opposite
steps and a constructed original parametricity residual. -/
theorem large {a} (d m n : Nat) (P : ContractionTree .term (a+1))
    (C : ContractionTree .term ((m+1)+n)) (selected : Fin (m+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate ((a+1)+(m+n)) .term) [],
      Rewrite (Graft.net (P.atDepth (d+2))
        ((left d C).reboundary (by congr 1 <;> omega) rfl)
        ⟨selected.val,by have:=selected.isLt;omega⟩)
        (.input ⟨0,by simp;omega⟩) A (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (P.atDepth (d+2))
        ((right d (m+1) n).reboundary (by congr 1 <;> omega) rfl)
        ⟨selected.val,by have:=selected.isLt;omega⟩)
        (.input ⟨0,by simp;omega⟩) B (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  let f := IsolatedFamily.largeLeftAtIso d m n selected
  let g := IsolatedFamily.largeRightAtIso d m n selected
  obtain ⟨D,l,inputs⟩ := PrivateReindex.presentation (by omega : (m+n)+1=(m+1)+n) f C
  have same : ∀ i, l.inputs.toFun i = g.inputs.toFun i :=
    fun i => (inputs i).trans (IsolatedFamily.largeAt_same_inputs d m n selected i)
  let hi : List.replicate ((m+1)+n) Wire.term = List.replicate ((m+n)+1) Wire.term := by congr 1 <;> omega
  let li := l.trans (BoundaryIso.interfaceEquality (left d C) hi rfl)
  let ri := g.trans (BoundaryIso.interfaceEquality (right d (m+1) n) hi rfl)
  obtain ⟨A,B,left,right,⟨w⟩⟩ := IsolatedCopy.large d m n P D
  have synchronized : ∀ i, li.inputs.toFun i = ri.inputs.toFun i := by
    intro i
    exact (targetCast_inputs l hi rfl i).trans
      ((congrArg (Fin.cast (congrArg List.length hi)) (same i)).trans
        (targetCast_inputs g hi rfl i).symm)
  apply transfer P li ri synchronized
    ⟨selected.val,by have:=selected.isLt;omega⟩ _ left right w
  apply Fin.ext
  change (li.inputs.toFun ⟨0,by simp⟩).val = selected.val
  rw [targetCast_inputs,inputs]
  have first := IsolatedFamily.largeLeftAtIso_first d m n selected
  have first' : (f.inputs.toFun ⟨0,by simp⟩).val = selected.val := by
    have picked := Port.input.inj ((f.map_input ⟨0,by simp⟩).symm.trans first)
    exact congrArg Fin.val picked
  exact first'

/-- Copying any originally selected small member has genuine opposite
steps and a constructed original parametricity residual. -/
theorem small {a} (d m n : Nat) (P : ContractionTree .term (a+1))
    (C : ContractionTree .term (m+(n+1))) (selected : Fin (n+1)) :
    ∃ A B : Hypernet (d+2) (List.replicate ((a+1)+(m+n)) .term) [],
      Rewrite (Graft.net (P.atDepth (d+2))
        ((left d C).reboundary (by congr 1 <;> omega) rfl)
        ⟨m+selected.val,by have:=selected.isLt;omega⟩)
        (.input ⟨0,by simp;omega⟩) A (.input ⟨0,by simp;omega⟩) ∧
      Rewrite (Graft.net (P.atDepth (d+2))
        ((right d m (n+1)).reboundary (by congr 1 <;> omega) rfl)
        ⟨m+selected.val,by have:=selected.isLt;omega⟩)
        (.input ⟨0,by simp;omega⟩) B (.input ⟨0,by simp;omega⟩) ∧
      Nonempty (FillingWitness template A B) := by
  let f := IsolatedFamily.smallLeftAtIso d m n selected
  let g := IsolatedFamily.smallRightAtIso d m n selected
  obtain ⟨D,l,inputs⟩ := PrivateReindex.presentation (by omega : (m+n)+1=m+(n+1)) f C
  have same : ∀ i, l.inputs.toFun i = g.inputs.toFun i :=
    fun i => (inputs i).trans (IsolatedFamily.smallAt_same_inputs d m n selected i)
  let hi : List.replicate (m+(n+1)) Wire.term = List.replicate ((m+n)+1) Wire.term := by congr 1 <;> omega
  let li := l.trans (BoundaryIso.interfaceEquality (left d C) hi rfl)
  let ri := g.trans (BoundaryIso.interfaceEquality (right d m (n+1)) hi rfl)
  obtain ⟨A,B,left,right,⟨w⟩⟩ := IsolatedCopy.small d m n P D
  have synchronized : ∀ i, li.inputs.toFun i = ri.inputs.toFun i := by
    intro i
    exact (targetCast_inputs l hi rfl i).trans
      ((congrArg (Fin.cast (congrArg List.length hi)) (same i)).trans
        (targetCast_inputs g hi rfl i).symm)
  apply transfer P li ri synchronized
    ⟨m+selected.val,by have:=selected.isLt;omega⟩ _ left right w
  apply Fin.ext
  change (li.inputs.toFun ⟨0,by simp⟩).val = m+selected.val
  rw [targetCast_inputs,inputs]
  have first := IsolatedFamily.smallLeftAtIso_first d m n selected
  have first' : (f.inputs.toFun ⟨0,by simp⟩).val = m+selected.val := by
    have picked := Port.input.inj ((f.map_input ⟨0,by simp⟩).symm.trans first)
    exact congrArg Fin.val picked
  exact first'

end Hypernets.Copying.Parametricity.LiteralCopy

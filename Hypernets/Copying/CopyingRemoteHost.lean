import Hypernets.Copying.CopyingRemoteSource
import Hypernets.Copying.CopyingRemoteCertificates
import Hypernets.Copying.CopyingRemoteCut
import Hypernets.Copying.CopyingRemotePair

/-! Actual whole-graph remote copying diagrams in the original specimen.
The first entered hole and the complete retained prefix determine a finite
common-context cut. Its two expanded sources are proved to be literal grafts,
so every selected original input has a proved diagram in the actual host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.RemoteContext
open Graph Opening Combined ContractionTree
variable {d m n k h : Nat} {I O : List Wire}
    (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (closed : HoleFree (C.expand L))
    (P : ContractionTree .term (m+1)) (f : Occurrence (P.atDepth d) C)
    (e : C.Edge) (name : Nat)
    (label : C.edgeLabel e = primitiveLabel d
      (.hole ⟨name,List.replicate (n+1) .term,environmentInterface k h⟩))
    (j : Fin (n+1))
    (link : f.ports (.output 0) = C.sourcePort e
      ⟨j.val,by rw [label,primitive_input]; simp [primitiveSignature]⟩)

include cert free closed label j link in
/-- Any actual prefix entering any original shallow copying input has one
original rewrite on each side and a complete original residual specimen,
with independently proved exact sharing corrections. -/
theorem diagram :
    ∃ X Y : Hypernet d I O, ∃ v : X.Vertex, ∃ w : Y.Vertex,
      Rewrite (C.expand L) (Net.Expansion.host C L (f.ports (.input ⟨0,by simp⟩))) X v ∧
      Rewrite (C.expand R) (Net.Expansion.host C R (f.ports (.input ⟨0,by simp⟩))) Y w ∧
      Nonempty (TwoSidedResidual X v Y w) := by
  let hi : (alphabet d).signature.input (C.edgeLabel e) = List.replicate (n+1) Wire.term := by
    rw [label,primitive_input]; rfl
  let ho : (alphabet d).signature.output (C.edgeLabel e) = environmentInterface k h := by
    rw [label,primitive_output]; rfl
  let U := (L e).reboundary hi ho
  let V := (R e).reboundary hi ho
  have rel : Pair U V := pair_reboundary ((cert e).relation_at_hole label closed) hi ho
  obtain ⟨X,Y,left,right,⟨res⟩⟩ := Pair.graft_diagram P rel j
  let source := occurrence C P f e name label j link
  let liso := sourceIso P name j U C f e label link L
    (fun x => (treeCopies C cert P f x).1) (DeepIso.refl _)
  let riso := sourceIso P name j V C f e label link R
    (fun x => (treeCopies C cert P f x).2) (DeepIso.refl _)
  have lstep := left.rename liso.symm (DeepIso.refl _)
  have rstep := right.rename riso.symm (DeepIso.refl _)
  have both := RemoteCut.diagram C source cert free
    (a := .input ⟨0,by simp; omega⟩) lstep rstep res
  have token : source.ports (.input ⟨0,by simp; omega⟩) = f.ports (.input ⟨0,by simp⟩) :=
    occurrence_input C P f e name label j link
  rw [token] at both
  exact ⟨_,_,_,_,both⟩


/-- The original copying pair itself determines its complete ordered input
and output interfaces. No scoping or closed-program restriction is added. -/
theorem pair_boundaries {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    ∃ n k h, I = List.replicate (n+1) .term ∧ O = environmentInterface k h := by
  cases pair with
  | witness _ literal _ =>
    cases literal with
    | copy T H copyable free => exact ⟨_,_,_,rfl,rfl⟩

/-- The actual arbitrary original hole's interfaces are recovered from its
proved copying replacement. This consumes the exact first-entry classification
without any normalized-hole or additional matching premise. -/
theorem any_hole_diagram {d I O m} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (closed : HoleFree (C.expand L))
    (P : ContractionTree .term (m+1)) (f : Occurrence (P.atDepth d) C)
    (e : C.Edge) (name : Hole) (label : C.edgeLabel e = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length)
    (link : f.ports (.output 0) = C.sourcePort e i) :
    ∃ X Y : Hypernet d I O, ∃ v : X.Vertex, ∃ w : Y.Vertex,
      Rewrite (C.expand L) (Net.Expansion.host C L (f.ports (.input ⟨0,by simp⟩))) X v ∧
      Rewrite (C.expand R) (Net.Expansion.host C R (f.ports (.input ⟨0,by simp⟩))) Y w ∧
      Nonempty (TwoSidedResidual X v Y w) := by
  have rel := (cert e).relation_at_hole label closed
  obtain ⟨n,k,h,hi,ho⟩ := pair_boundaries rel
  have input : name.input = List.replicate (n+1) Wire.term := by
    simpa only [label,primitive_input,primitiveSignature] using hi
  have output : name.output = environmentInterface k h := by
    simpa only [label,primitive_output,primitiveSignature] using ho
  have same : name = ⟨name.name,List.replicate (n+1) .term,environmentInterface k h⟩ := by
    cases name
    congr
  let j : Fin (n+1) := ⟨i.val,by
    have bound := i.isLt
    have length := congrArg List.length hi
    simp only [List.length_replicate] at length
    omega⟩
  have label' : C.edgeLabel e = primitiveLabel d
      (.hole ⟨name.name,List.replicate (n+1) .term,environmentInterface k h⟩) :=
    label.trans (congrArg (fun h => primitiveLabel d (.hole h)) same)
  apply diagram C cert free closed P f e name.name label' j
  simpa only [j,Fin.eta] using link

end Hypernets.Copying.CopyingTemplate.RemoteContext

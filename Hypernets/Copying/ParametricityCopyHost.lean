import Hypernets.Copying.ParametricityPairCopy
import Hypernets.Copying.CopyingRemoteSource
import Hypernets.Copying.CopyingRemoteCertificates
import Hypernets.Copying.CommonContextRobustness

/-! The actual first entered parametricity hole and its retained prefix
supply one computed common-context cut. Its literal graft source is proved,
and the original paired residual is inserted with all untouched certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.CopyHost
open Graph Opening Combined ContractionTree CopyingTemplate.RemoteContext

private theorem pair_reboundary {d I O J K} {G H : Hypernet d I O}
    (pair : Pair G H) (hi : I=J) (ho : O=K) :
    Pair (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using pair

/-- An actual prefix entering a complete original parametricity component
has a one-step/one-step exact quasi-specimen in the original full host. -/
theorem diagram {d a b} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (P : ContractionTree .term (a+1)) (f : Occurrence (P.atDepth d) C)
    (e : C.Edge) (name : Nat)
    (label : C.edgeLabel e = primitiveLabel d (.hole ⟨name,List.replicate (b+1) .term,[]⟩))
    (j : Fin (b+1))
    (link : f.ports (.output 0) = C.sourcePort e
      ⟨j.val,by rw [label,primitive_input];simp [primitiveSignature]⟩) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports (.input ⟨0,by simp⟩)))⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports (.input ⟨0,by simp⟩)))⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq s t := by
  let hi : (alphabet d).signature.input (C.edgeLabel e) = List.replicate (b+1) Wire.term := by
    rw [label,primitive_input];rfl
  let ho : (alphabet d).signature.output (C.edgeLabel e) = [] := by rw [label,primitive_output];rfl
  let U := (L e).reboundary hi ho
  let V := (R e).reboundary hi ho
  have rel : Pair U V := pair_reboundary ((cert e).relation_at_hole label leftClosed) hi ho
  obtain ⟨X,Y,left,right,⟨w⟩⟩ := Pair.graft_diagram P rel j
  let source := occurrence C P f e name label j link
  let liso := sourceIso P name j U C f e label link L
    (fun x => (treeCopies C cert P f x).1) (DeepIso.refl _)
  let riso := sourceIso P name j V C f e label link R
    (fun x => (treeCopies C cert P f x).2) (DeepIso.refl _)
  have lstep := left.rename liso.symm (DeepIso.refl X)
  have rstep := right.rename riso.symm (DeepIso.refl Y)
  have both := CommonContextCut.diamond C source cert free w
    (.input ⟨0,by simp;omega⟩) (List.getElem_replicate _)
    (a := .input ⟨0,by simp;omega⟩) lstep rstep template_outputClosed leftClosed rightClosed
  have token : source.ports (.input ⟨0,by simp;omega⟩) = f.ports (.input ⟨0,by simp⟩) :=
    occurrence_input C P f e name label j link
  rw [token] at both
  exact ⟨_,_,StateClass.project (.lift (.rewrite both.1)),
    StateClass.project (.lift (.rewrite both.2.1)),both.2.2⟩

/-- The original Figure20 pair determines the full term-only input row and
empty output row, including the possible empty family. -/
theorem pair_boundaries {d I O} {G H : Hypernet d I O} (pair : Pair G H) :
    ∃ n, I=List.replicate n .term ∧ O=[] := by
  cases pair with
  | witness _ literal _ =>
    cases literal with
    | families d C => exact ⟨_,rfl,rfl⟩

/-- The exact first shallow input obtained from the actual copy trace is
sufficient to construct the whole original host diagram. Its existing input
makes the entered family nonempty; no new scope assumption is introduced. -/
theorem any_hole_diagram {d a} (C : Hypernet d [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L)) (rightClosed : HoleFree (C.expand R))
    (P : ContractionTree .term (a+1)) (f : Occurrence (P.atDepth d) C)
    (e : C.Edge) (name : Hole) (label : C.edgeLabel e = primitiveLabel d (.hole name))
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length)
    (link : f.ports (.output 0) = C.sourcePort e i) :
    ∃ s t,
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand L,(.rewrite,Net.Expansion.host C L (f.ports (.input ⟨0,by simp⟩)))⟩) s ∧
      StateClass.machine.step
        (StateClass.ofState ⟨d,C.expand R,(.rewrite,Net.Expansion.host C R (f.ports (.input ⟨0,by simp⟩)))⟩) t ∧
      (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq s t := by
  have pair := (cert e).relation_at_hole label leftClosed
  obtain ⟨n,hi,ho⟩ := pair_boundaries pair
  cases n with
  | zero => exact Fin.elim0 (Fin.cast (congrArg List.length hi) i)
  | succ n =>
    have input : name.input = List.replicate (n+1) Wire.term := by
      simpa only [label,primitive_input,primitiveSignature] using hi
    have output : name.output = [] := by
      simpa only [label,primitive_output,primitiveSignature] using ho
    have same : name = ⟨name.name,List.replicate (n+1) .term,[]⟩ := by
      cases name
      congr
    let j : Fin (n+1) := ⟨i.val,by
      have bound:=i.isLt
      have length:=congrArg List.length hi
      simp only [List.length_replicate] at length
      omega⟩
    have label' : C.edgeLabel e = primitiveLabel d (.hole ⟨name.name,List.replicate (n+1) .term,[]⟩) :=
      label.trans (congrArg (fun h => primitiveLabel d (.hole h)) same)
    apply diagram C cert free leftClosed rightClosed P f e name.name label' j
    simpa only [j,Fin.eta] using link

end Hypernets.Copying.Parametricity.CopyHost

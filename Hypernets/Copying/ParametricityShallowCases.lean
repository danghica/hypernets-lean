import Hypernets.Copying.ParametricityBetaExtraction
import Hypernets.Copying.ParametricityShallowHost
import Hypernets.Copying.ParametricityPairBeta

/-! Every actual shallow selected function yields its complete original
family diagram in the actual original host. This discharges both shallow
fields of the exhaustive nine-rule robustness assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph Opening Combined

private theorem pair_reboundary {d I O J K} {G H : Hypernet d I O}
    (pair : Pair G H) (hi : I=J) (ho : O=K) :
    Pair (G.reboundary hi ho) (H.reboundary hi ho) := by
  cases hi;cases ho
  simpa only [Net.reboundary_refl] using pair

namespace ShallowCases
variable {d} (C : Hypernet (d+1) [.term] []) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (leftClosed : HoleFree (C.expand L))
    (app : Occurrence (primitiveNet (d+1) (.operation .app)) C)
    (labels : ∀ x, C.edgeLabel (app.edges x) = primitiveLabel (d+1) (.operation .app))
    (e : C.Edge) (name : Hole) (label : C.edgeLabel e = primitiveLabel (d+1) (.hole name))
    (i : Fin ((alphabet (d+1)).signature.input (C.edgeLabel e)).length)
    (link : app.ports (.output (0 : Fin 2)) = C.sourcePort e i)
    (leftRoot : Search.RootedFrom (C.expand L) 0
      (.rewrite,Net.Expansion.host C L (app.ports (.input (0 : Fin 1)))))
    (rightRoot : Search.RootedFrom (C.expand R) 0
      (.rewrite,Net.Expansion.host C R (app.ports (.input (0 : Fin 1)))))
include cert free leftClosed labels label link leftRoot rightRoot

/-- An actually entered original family has positive term-input arity.
Its exact selected member supplies the full forward host diagram. -/
theorem forward (U : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand L,
        (.rewrite,Net.Expansion.host C L (app.ports (.input (0 : Fin 1))))⟩) successor) :
    RobustnessAssembly.ForwardClause C (R := R) (app.ports (.input (0 : Fin 1))) U successor := by
  have pair := (cert e).relation_at_hole label leftClosed
  obtain ⟨n,hi,ho⟩ := CopyHost.pair_boundaries pair
  cases n with
  | zero => exact Fin.elim0 (Fin.cast (congrArg List.length hi) i)
  | succ b =>
    have input : name.input = List.replicate (b+1) Wire.term := by
      have result := hi
      rw [label,Hypernets.Copying.primitive_input] at result
      exact result
    have output : name.output = [] := by
      have result := ho
      rw [label,Hypernets.Copying.primitive_output] at result
      exact result
    have same : name = ⟨name.name,List.replicate (b+1) .term,[]⟩ := by cases name;congr
    have label' := label.trans (congrArg (fun h => primitiveLabel (d+1) (.hole h)) same)
    let j : Fin (b+1) := ⟨i.val,by
      have bound:=i.isLt
      have length:=congrArg List.length hi
      simp only [List.length_replicate] at length
      omega⟩
    have rel : Pair (ShallowHost.leftPart C e name.name label' (L := L))
        (ShallowHost.rightPart C e name.name label' (R := R)) := pair_reboundary pair _ _
    obtain ⟨n,⟨diagram⟩⟩ := Pair.read_diagram rel j
    exact ShallowHost.forward_case C cert app labels e name.name label' j
      (by simpa only [j,Fin.eta] using link) diagram free leftClosed leftRoot rightRoot U step

/-- The same exact originally entered family supplies the converse diagram
even when the independently given rewrite is on the right. -/
theorem converse (P : CostOrder) {successor : StateClass}
    (step : StateClass.machine.step
      (StateClass.ofState ⟨d+1,C.expand R,
        (.rewrite,Net.Expansion.host C R (app.ports (.input (0 : Fin 1))))⟩) successor) :
    RobustnessAssembly.ConverseClause C (L := L) (app.ports (.input (0 : Fin 1))) P successor := by
  have pair := (cert e).relation_at_hole label leftClosed
  obtain ⟨n,hi,ho⟩ := CopyHost.pair_boundaries pair
  cases n with
  | zero => exact Fin.elim0 (Fin.cast (congrArg List.length hi) i)
  | succ b =>
    have input : name.input = List.replicate (b+1) Wire.term := by
      have result := hi
      rw [label,Hypernets.Copying.primitive_input] at result
      exact result
    have output : name.output = [] := by
      have result := ho
      rw [label,Hypernets.Copying.primitive_output] at result
      exact result
    have same : name = ⟨name.name,List.replicate (b+1) .term,[]⟩ := by cases name;congr
    have label' := label.trans (congrArg (fun h => primitiveLabel (d+1) (.hole h)) same)
    let j : Fin (b+1) := ⟨i.val,by
      have bound:=i.isLt
      have length:=congrArg List.length hi
      simp only [List.length_replicate] at length
      omega⟩
    have rel : Pair (ShallowHost.leftPart C e name.name label' (L := L))
        (ShallowHost.rightPart C e name.name label' (R := R)) := pair_reboundary pair _ _
    obtain ⟨n,⟨diagram⟩⟩ := Pair.read_diagram rel j
    exact ShallowHost.converse_case C cert app labels e name.name label' j
      (by simpa only [j,Fin.eta] using link) diagram free leftClosed leftRoot rightRoot P step

end ShallowCases

/-- Both shallow-beta obligations are discharged by the actual arbitrary
selected-family diagrams, source extraction and original whole-host cuts. -/
theorem shallowBetaCases : RobustnessAssembly.ShallowBetaCases := by
  constructor
  ·
    intro d C L R cert free leftClosed rightClosed v leftRoot rightRoot k h B a q label U successor step
    obtain ⟨app,point,labels,i,link⟩ := LambdaEntryOverlap.beta_entry C cert template_lambdaEntries a
    have result := ShallowCases.forward C cert free leftClosed app labels a.lam.1 q label i link
      (point.symm ▸ leftRoot) (point.symm ▸ rightRoot) U (point.symm ▸ step)
    simpa only [point] using result
  ·
    intro d C L R cert free leftClosed rightClosed v leftRoot rightRoot k h B a q label P successor step
    obtain ⟨app,point,labels,i,link⟩ := LambdaEntryOverlap.beta_entry C
      (fun e => (cert e).converse) converse_lambdaEntries a
    have result := ShallowCases.converse C cert free leftClosed app labels a.lam.1 q label i link
      (point.symm ▸ leftRoot) (point.symm ▸ rightRoot) P (point.symm ▸ step)
    simpa only [point] using result

/-- Full forward robustness of the literal Figure20 parametricity family
for every original recursive unrestricted specimen and all original rules. -/
theorem template_robust (U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Robust
      .improvement .improvement U :=
  RobustnessAssembly.robust_of_shallow shallowBetaCases U

/-- Full converse robustness of the same original directed family, retaining
the original reverse cost inequality for every actual right successor. -/
theorem template_robust_converse (P : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).opposite.Robust
      .overhead P .overhead :=
  RobustnessAssembly.converse_robust_of_shallow shallowBetaCases P

end Hypernets.Copying.Parametricity

import Hypernets.Copying.InterfacePermutation

/-! The concrete box-permutation graph pair of Figure 21. No observational
 equivalence or machine transition is assumed by this structural construction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace InterfacePermutation
/-- A boundary isomorphism with prescribed action factors through actual interface permutation. -/
def realize {d I O} {G H : Hypernet d I O} (f : BoundaryIso G H)
    (p : TypedPermutation O) (hi : ∀ i, f.inputs.toFun i = i)
    (ho : ∀ i, f.outputs.toFun i = p.bijection.toFun i) : DeepIso (net G p) H :=
  (congr (compensate f p hi ho) p).trans (roundtrip H p.symm).symm
end InterfacePermutation

namespace BoxPermutation
variable {d n k h : Nat}
    (G : Hypernet d [.term] (environmentInterface (n+k) h)) (p : Pair n k h)

/-- Permute the body's free boundary, then undo that action outside the box.
Bound outputs stay fixed. Both sides have exactly the same external interface. -/
def right : Hypernet (d+1) [.thunk n] (environmentInterface k h) :=
  InterfacePermutation.net (box (bound := n) (freeVariables := k)
    (InterfacePermutation.net G p.body)) p.outer.symm

/-- The literal Figure 21 pair: permute the body on the left, or the outer
box on the right, using the paper's boundary-list convention. -/
inductive Step : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop where
  | permute {d n k h : Nat} (G : Hypernet d [.term] (environmentInterface (n+k) h)) (p : Pair n k h) :
      Step (box (bound := n) (freeVariables := k) (InterfacePermutation.net G p.body.symm))
        (InterfacePermutation.net (box (bound := n) (freeVariables := k) G) p.outer.symm)

/-- Carrier choices may differ on either side of the concrete rule. -/
inductive UpToIso : {d : Nat} → {I O : List Wire} → Hypernet d I O → Hypernet d I O → Prop where
  | witness {d : Nat} {I O : List Wire} {G H A B : Hypernet d I O} (left : DeepIso G A)
      (step : Step A B) (right : DeepIso B H) : UpToIso G H

/-- All primitive-label restrictions, including language, focus and hole exclusion,
are exactly preserved; permutations do not remove any nested body. -/
theorem allLabels_right (P : Primitive → Prop) : AllLabels P (right G p) ↔ AllLabels P G := by
  constructor
  · intro hp
    exact hp (0 : Fin 1)
  · intro hp e
    exact hp

/-- The raw rule is realised by a supplied ordered body isomorphism with the exact pair action. -/
theorem of_bodyIso {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (p : Pair n k h) (f : BoundaryIso G H)
    (action : ∀ i, f.outputs.toFun i = p.body.bijection.toFun i) :
    UpToIso (box (bound := n) (freeVariables := k) G)
      (InterfacePermutation.net (box (bound := n) (freeVariables := k) H) p.outer.symm) := by
  have body := InterfacePermutation.compensate f p.body (fun _ => f.input_singleton _) action
  exact .witness (box_congr body) (.permute H p) (DeepIso.refl _)

/-- The compensated normal form follows from the literal paper rule up to isomorphism. -/
theorem normalized : UpToIso (box (bound := n) (freeVariables := k) G) (right G p) :=
  of_bodyIso p (InterfacePermutation.iso G p.body) (InterfacePermutation.iso_output G p.body)

/-- An ordered corolla isomorphism must fix each output position individually. -/
theorem box_output_fixed {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (f : BoundaryIso (box (bound := n) (freeVariables := k) G)
      (box (bound := n) (freeVariables := k) H)) (i : Fin (environmentInterface k h).length) :
    f.ports.toFun (.output i) = .output i := by
  have eq := f.target (0 : Fin 1)
  have entry :=  congrArg (fun xs => xs[i.val]?) eq
  simpa [box,Net.corolla,nextAlphabet,List.map_map,List.getElem?_eq_getElem,i.isLt] using entry

/-- Therefore a nontrivial free action cannot be silently treated as a box isomorphism. -/
theorem nontrivial_not_ordered {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (p : TypedPermutation (environmentInterface k h))
    (moves : ∃ i, p.bijection.toFun i ≠ i) :
    ¬ ∃ f : BoundaryIso (box (bound := n) (freeVariables := k) G)
        (box (bound := n) (freeVariables := k) H),
      ∀ i, f.ports.toFun (.output i) = .output (p.bijection.toFun i) := by
  rintro ⟨f,act⟩
  obtain ⟨i,ne⟩ := moves
  exact ne (Port.output.inj ((act i).symm.trans (box_output_fixed f i)))
end BoxPermutation
end Hypernets.Copying

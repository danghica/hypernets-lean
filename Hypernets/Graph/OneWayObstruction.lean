import Hypernets.Graph.OneWay

/-! The single-hole one-way obstruction of Appendix C, Lemma 26(2). -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}
    {kind : Op → OperationKind} {C : Hypernet ops d [.term] []}

namespace Focussed
/-- The actual state obtained from a focus-free filling, once global hole
freedom of the result is proved. These conditions are not inferred from typing. -/
noncomputable def filledState (f : Focussed C) (hole : C.Edge) (different : f.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (free : FocusFree H) (closed : HoleFree (C.plug hole H)) : State ops d :=
  ⟨C.plug hole H, f.plug hole different H free, closed⟩

/-- Lemma 26(2): a non-operation path to the context's focus source survives
as an obstruction to rootedness after any one-way focus-free filling.
The path may contain the hole, including repeated occurrences of it. -/
theorem oneWay_not_rooted (f : Focussed C) (hole : C.Edge) (different : f.edge ≠ hole)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (free : FocusFree H) (closed : HoleFree (C.plug hole H)) (one : OneWay H)
    {es : List C.Edge} (path : C.Path es) {last : C.Edge}
    (endEdge : es.getLast? = some last) (target : f.source ∈ C.target last)
    {bad : C.Edge} (mem : bad ∈ es) (nonop : ¬ IsOperation ops d (C.edgeLabel bad)) :
    ¬ State.Rooted kind (f.filledState hole different H free closed) := by
  intro rooted
  have root := State.rooted_focus_operationReachable rooted
  exact nonop (OneWayReplacement.path_operations C hole H one (FocusErasure.source_term f) root
    path endEdge target bad mem)

/-- The single-hole paired version: when at least one filling is one-way,
at least one of the two filled states is not rooted. This is the one-hole
instance of the output-closure argument, without assuming a specimen interface. -/
theorem oneWay_pair_not_rooted (f : Focussed C) (hole : C.Edge) (different : f.edge ≠ hole)
    (H K : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))
    (hf : FocusFree H) (kf : FocusFree K)
    (hc : HoleFree (C.plug hole H)) (kc : HoleFree (C.plug hole K))
    (one : OneWay H ∨ OneWay K)
    {es : List C.Edge} (path : C.Path es) {last : C.Edge}
    (endEdge : es.getLast? = some last) (target : f.source ∈ C.target last)
    {bad : C.Edge} (mem : bad ∈ es) (nonop : ¬ IsOperation ops d (C.edgeLabel bad)) :
    ¬ State.Rooted kind (f.filledState hole different H hf hc) ∨
      ¬ State.Rooted kind (f.filledState hole different K kf kc) := by
  cases one with
  | inl one => exact Or.inl (f.oneWay_not_rooted hole different H hf hc one path endEdge target mem nonop)
  | inr one => exact Or.inr (f.oneWay_not_rooted hole different K kf kc one path endEdge target mem nonop)

end Focussed
end Hypernets.Linear

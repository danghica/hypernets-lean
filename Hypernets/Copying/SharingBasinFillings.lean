import Hypernets.Copying.BasinExpansionOccurrence
import Hypernets.Copying.SharingTreeFillings

/-! Original recursive certificates restrict to a maximal sharing context and
produce actual complete sharing-tree matches on both sides of the specimen. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingBasin
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {s : ShareSort} (S : C.RootedBasin s.wire)
    (labels : ∀ e, S.chosen e → Eligible C s e)
    (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)
    (closed : HoleFree (C.expand L))

noncomputable abbrev selectedContext := context S labels inputs distinct boundary
abbrev selectedLeft (e : S.Edge) := L e.val
abbrev selectedRight (e : S.Edge) := R e.val

include cert in
omit closed trees in
theorem selectedCertificates : ∀ e,
    DeepFillingEdge T (selectedContext C S labels inputs distinct boundary).net
      (selectedLeft C (L := L) S) (selectedRight C (R := R) S) e := by
  intro e
  cases cert e.val with
  | retained l r => exact .retained l r
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner l r

include closed in
theorem selectedClosed : HoleFree
    ((selectedContext C S labels inputs distinct boundary).net.expand (selectedLeft C (L := L) S)) :=
  (BasinExpansion.occurrence S labels inputs distinct boundary L).allLabels _ closed

noncomputable abbrev leftTree :=
  ((selectedContext C S labels inputs distinct boundary).left_sharingTreeGraph
    (selectedCertificates C cert S labels inputs distinct boundary) trees
    (selectedClosed C S labels inputs distinct boundary closed)).tree

noncomputable abbrev rightTree :=
  ((selectedContext C S labels inputs distinct boundary).right_sharingTreeGraph
    (selectedCertificates C cert S labels inputs distinct boundary) trees
    (selectedClosed C S labels inputs distinct boundary closed)).tree

/-- Both recovered primitive trees retain the original common-context holes
and exact recursive template pairs, rather than identifying all sharing trees. -/
noncomputable def treeWitness : FillingWitness T
    ((leftTree C cert trees S labels inputs distinct boundary closed).atDepth d)
    ((rightTree C cert trees S labels inputs distinct boundary closed).atDepth d) :=
  (selectedContext C S labels inputs distinct boundary).treeWitness
    (selectedCertificates C cert S labels inputs distinct boundary) trees
    (selectedClosed C S labels inputs distinct boundary closed)

/-- The recovered left tree occurs in the actual original left expansion. -/
noncomputable def leftOccurrence : Occurrence
    ((leftTree C cert trees S labels inputs distinct boundary closed).atDepth d) (C.expand L) :=
  (Occurrence.ofIso ((selectedContext C S labels inputs distinct boundary).left_sharingTreeGraph
    (selectedCertificates C cert S labels inputs distinct boundary) trees
    (selectedClosed C S labels inputs distinct boundary closed)).treeIso).comp
      (BasinExpansion.occurrence S labels inputs distinct boundary L)

/-- The right match uses the same selected original boundary and all its holes. -/
noncomputable def rightOccurrence : Occurrence
    ((rightTree C cert trees S labels inputs distinct boundary closed).atDepth d) (C.expand R) :=
  (Occurrence.ofIso ((selectedContext C S labels inputs distinct boundary).right_sharingTreeGraph
    (selectedCertificates C cert S labels inputs distinct boundary) trees
    (selectedClosed C S labels inputs distinct boundary closed)).treeIso).comp
      (BasinExpansion.occurrence S labels inputs distinct boundary R)

theorem left_input (i : Fin (List.replicate inputs.length s.wire).length) :
    (leftOccurrence C cert trees S labels inputs distinct boundary closed).ports (.input i) =
      Net.Expansion.host C L (inputs.get ⟨i.val,by simpa using i.isLt⟩).val := rfl

theorem right_input (i : Fin (List.replicate inputs.length s.wire).length) :
    (rightOccurrence C cert trees S labels inputs distinct boundary closed).ports (.input i) =
      Net.Expansion.host C R (inputs.get ⟨i.val,by simpa using i.isLt⟩).val := rfl

theorem left_output :
    (leftOccurrence C cert trees S labels inputs distinct boundary closed).ports (.output 0) =
      Net.Expansion.host C L S.output := rfl

theorem right_output :
    (rightOccurrence C cert trees S labels inputs distinct boundary closed).ports (.output 0) =
      Net.Expansion.host C R S.output := rfl

end Hypernets.Copying.SharingBasin

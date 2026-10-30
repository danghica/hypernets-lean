import Hypernets.Copying.SharingRootOrigin
import Hypernets.Copying.SharingContextReachability
import Hypernets.Copying.SharingBasinFillings
import Hypernets.Graph.RootedBasinBoundary

/-! A real local tree match supplies a maximal original common sharing context.
Its selected input stays first; all unused predecessor branches are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- A selected original vertex becomes the first actual boundary input of
the computed maximal component; no complete occurrence or cut is a premise. -/
theorem component {s : ShareSort} {m} (A : ContractionTree s m)
    (f : Occurrence (A.atDepth d) (C.expand L))
    {head : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel head = primitiveLabel d p)
    (source : f.ports (.output 0) ∈ (C.expand L).source head)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (notHole : ∀ h, p ≠ .hole h)
    (i : Fin (List.replicate m s.wire).length) {v : C.Vertex}
    (entry : f.ports (.input i) = Net.Expansion.host C L v)
    (excluded : ∀ e, SharingLabel d s (C.edgeLabel e) → v ∉ C.target e) :
    ∃ S : C.RootedBasin s.wire, ∃ labels : ∀ e, S.chosen e → SharingBasin.Eligible C s e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex,
        a.val = v ∧ (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        Net.Expansion.host C L S.output = f.ports (.output 0) := by
  obtain ⟨q,out,sharing,target,terminal⟩ := SharingRootOrigin.tree_root C cert trees A f label source nonsharing notHole
  let S := SharingBasin.basin C s (f.edges A.root).1 q sharing target terminal
  have labels (e : C.Edge) (selected : S.chosen e) : SharingBasin.Eligible C s e := selected.1
  obtain ⟨e,n,mem,_⟩ := A.input_reaches_root i
  have selected : S.chosen (f.edges e).1 := SharingRootOrigin.tree_selected C cert trees A f e
  have actual : Net.Expansion.host C L v ∈ (C.expand L).source (f.edges e) :=
    entry ▸ f.matchEmbedding.source_mem mem
  have old := Search.Expansion.source_owner C L actual
  let a : S.Vertex := ⟨v,(f.edges e).1,selected,Or.inl old⟩
  have input : S.Input a := by
    rintro ⟨b,h⟩
    exact excluded b.val (labels b.val b.property) ((S.mem_target a b).mp h)
  obtain ⟨rest,distinct,boundary⟩ := S.first_input_order a input
  exact ⟨S,labels,a,rest,rfl,distinct,boundary,out⟩

/-- Rooted term positions cannot have a sharing producer; this is proved from
actual operation reachability, not added as an exclusion assumption. -/
theorem term_component {m} (A : ContractionTree .term m)
    (f : Occurrence (A.atDepth d) (C.expand L))
    {head : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel head = primitiveLabel d p)
    (source : f.ports (.output 0) ∈ (C.expand L).source head)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (notHole : ∀ h, p ≠ .hole h)
    (i : Fin (List.replicate m Wire.term).length) {v : C.Vertex}
    (entry : f.ports (.input i) = Net.Expansion.host C L v)
    (reachable : Search.OperationReachable C v) :
    ∃ S : C.RootedBasin Wire.term, ∃ labels : ∀ e, S.chosen e → SharingBasin.Eligible C .term e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex,
        a.val = v ∧ (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        Net.Expansion.host C L S.output = f.ports (.output 0) :=
  component C cert trees A f label source nonsharing notHole i entry
    (fun e sharing target => reachable.not_nonoperation_target sharing.not_operation target)

end Hypernets.Copying.MaximalSharing

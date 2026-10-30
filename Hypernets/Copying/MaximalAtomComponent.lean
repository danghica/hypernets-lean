import Hypernets.Copying.MaximalSharingComponent

/-! Actual instance producers place the selected atom references on the
boundary of the maximal sharing context, in their original operand order. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Opening Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- A nonsharing producer has an original host output. No sharing component
can also produce it, by the actual graph's unique-target law. -/
theorem producer_origin {s : ShareSort} {e : (C.expand L).Edge} {p : Primitive} {w}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (target : w ∈ (C.expand L).target e)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (notHole : ∀ h, p ≠ .hole h) :
    ∃ v, Net.Expansion.host C L v = w ∧
      ∀ a, SharingLabel d s (C.edgeLabel a) → v ∉ C.target a := by
  obtain ⟨copy⟩ := SharingRootOrigin.retained C cert trees label nonsharing
  have row : (C.expand L).target e = (C.target e.1).map (Net.Expansion.host C L) := by
    rcases e with ⟨e,x⟩
    simpa only [copy.only x] using copy.target_eq
  rw [row] at target
  obtain ⟨v,mem,eq⟩ := List.mem_map.mp target
  refine ⟨v,eq,?_⟩
  intro a sharing produced
  have same := C.target_unique produced mem
  subst a
  have original : C.edgeLabel e.1 = primitiveLabel d p :=
    (copy.primitive p).mp (by change (L e.1).edgeLabel e.2 = _ at label; simpa only [copy.only e.2] using label)
  rcases sharing with weak | contraction | ⟨h,n,hole,_,_⟩
  · exact (nonsharing s).1 (primitiveLabel_injective d (original.symm.trans weak))
  · exact (nonsharing s).2 (primitiveLabel_injective d (original.symm.trans contraction))
  · exact notHole h (primitiveLabel_injective d (original.symm.trans hole))

/-- A retained unary primitive exposes the same two original context ports.
Actual singleton rows determine those coordinates without choosing names. -/
theorem unary_primitive_origin {e : (C.expand L).Edge} {p : Primitive} {a b}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (source : (C.expand L).source e = [a]) (target : (C.expand L).target e = [b]) :
    ∃ v w, C.edgeLabel e.1 = primitiveLabel d p ∧ C.source e.1 = [v] ∧ C.target e.1 = [w] ∧
      Net.Expansion.host C L v = a ∧ Net.Expansion.host C L w = b := by
  obtain ⟨copy⟩ := SharingRootOrigin.retained C cert trees label nonsharing
  have src : (C.source e.1).map (Net.Expansion.host C L) = [a] := by
    have h : (C.expand L).source e = (C.source e.1).map (Net.Expansion.host C L) := by
      rcases e with ⟨e,x⟩
      simpa only [copy.only x] using copy.source_eq
    exact h.symm.trans source
  have tgt : (C.target e.1).map (Net.Expansion.host C L) = [b] := by
    have h : (C.expand L).target e = (C.target e.1).map (Net.Expansion.host C L) := by
      rcases e with ⟨e,x⟩
      simpa only [copy.only x] using copy.target_eq
    exact h.symm.trans target
  have slen : (C.source e.1).length = 1 := by simpa using congrArg List.length src
  have tlen : (C.target e.1).length = 1 := by simpa using congrArg List.length tgt
  obtain ⟨v,sv⟩ := List.length_eq_one_iff.mp slen
  obtain ⟨w,tw⟩ := List.length_eq_one_iff.mp tlen
  refine ⟨v,w,?_,sv,tw,?_,?_⟩
  · exact (copy.primitive p).mp (by change (L e.1).edgeLabel e.2 = _ at label; simpa only [copy.only e.2] using label)
  · simpa only [sv,List.map_cons,List.map_nil,List.cons.injEq,and_true] using src
  · simpa only [tw,List.map_cons,List.map_nil,List.cons.injEq,and_true] using tgt

/-- The actual selected instance and store derive the entire maximal atom
component. No boundary exclusion or guessed maximal match is assumed. -/
theorem atom_component {m} (A : ContractionTree .atom m)
    (f : Occurrence (A.atDepth d) (C.expand L))
    {store inst : (C.expand L).Edge}
    (storeLabel : (C.expand L).edgeLabel store = primitiveLabel d .store)
    (storeSource : f.ports (.output 0) ∈ (C.expand L).source store)
    (i : Fin (List.replicate m Wire.atom).length)
    (instanceLabel : (C.expand L).edgeLabel inst = primitiveLabel d .instanceEdge)
    (instanceTarget : f.ports (.input i) ∈ (C.expand L).target inst) :
    ∃ S : C.RootedBasin Wire.atom, ∃ _labels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex,
        Net.Expansion.host C L a.val = f.ports (.input i) ∧
        (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        Net.Expansion.host C L S.output = f.ports (.output 0) := by
  obtain ⟨v,entry,excluded⟩ := producer_origin C cert trees (s := .atom) instanceLabel instanceTarget
    (by intro t; constructor <;> intro h <;> cases h) (by intro h eq; cases eq)
  obtain ⟨S,labels,a,rest,aeq,nd,boundary,out⟩ := component C cert trees A f storeLabel storeSource
    (by intro t; constructor <;> intro h <;> cases h) (by intro h eq; cases eq) i entry.symm excluded
  exact ⟨S,labels,a,rest,aeq ▸ entry,nd,boundary,out⟩

/-- Both references of a same-store comparison remain the first two ordered
inputs of one maximal component; every unused predecessor branch is retained. -/
theorem atom_two_component {m} (A : ContractionTree .atom m)
    (f : Occurrence (A.atDepth d) (C.expand L))
    {store first second : (C.expand L).Edge}
    (storeLabel : (C.expand L).edgeLabel store = primitiveLabel d .store)
    (storeSource : f.ports (.output 0) ∈ (C.expand L).source store)
    (i j : Fin (List.replicate m Wire.atom).length) (distinct : i ≠ j)
    (firstLabel : (C.expand L).edgeLabel first = primitiveLabel d .instanceEdge)
    (firstTarget : f.ports (.input i) ∈ (C.expand L).target first)
    (secondLabel : (C.expand L).edgeLabel second = primitiveLabel d .instanceEdge)
    (secondTarget : f.ports (.input j) ∈ (C.expand L).target second) :
    ∃ S : C.RootedBasin Wire.atom, ∃ _labels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a b : S.Vertex, ∃ rest : List S.Vertex,
        Net.Expansion.host C L a.val = f.ports (.input i) ∧
        Net.Expansion.host C L b.val = f.ports (.input j) ∧
        (a::b::rest).Nodup ∧ (∀ x, x ∈ a::b::rest ↔ S.Input x) ∧
        Net.Expansion.host C L S.output = f.ports (.output 0) := by
  obtain ⟨v,entry,excluded⟩ := producer_origin C cert trees (s := .atom) firstLabel firstTarget
    (by intro t; constructor <;> intro h <;> cases h) (by intro h eq; cases eq)
  obtain ⟨w,entry',excluded'⟩ := producer_origin C cert trees (s := .atom) secondLabel secondTarget
    (by intro t; constructor <;> intro h <;> cases h) (by intro h eq; cases eq)
  obtain ⟨q,out,sharing,target,terminal⟩ := SharingRootOrigin.tree_root C cert trees A f storeLabel storeSource
    (by intro t; constructor <;> intro h <;> cases h) (by intro h eq; cases eq)
  let S := SharingBasin.basin C .atom (f.edges A.root).1 q sharing target terminal
  have labels (e : C.Edge) (selected : S.chosen e) : SharingBasin.Eligible C .atom e := selected.1
  obtain ⟨e,n,mem,_⟩ := A.input_reaches_root i
  obtain ⟨g,k,mem',_⟩ := A.input_reaches_root j
  have chosen : S.chosen (f.edges e).1 := SharingRootOrigin.tree_selected C cert trees A f e
  have chosen' : S.chosen (f.edges g).1 := SharingRootOrigin.tree_selected C cert trees A f g
  have actual : f.ports (.input i) ∈ (C.expand L).source (f.edges e) := f.matchEmbedding.source_mem mem
  have actual' : f.ports (.input j) ∈ (C.expand L).source (f.edges g) := f.matchEmbedding.source_mem mem'
  rw [← entry] at actual
  rw [← entry'] at actual'
  have old := Search.Expansion.source_owner C L actual
  have old' := Search.Expansion.source_owner C L actual'
  let a : S.Vertex := ⟨v,(f.edges e).1,chosen,Or.inl old⟩
  let b : S.Vertex := ⟨w,(f.edges g).1,chosen',Or.inl old'⟩
  have input : S.Input a := by
    rintro ⟨edge,h⟩
    exact excluded edge.val (labels edge.val edge.property) ((S.mem_target a edge).mp h)
  have input' : S.Input b := by
    rintro ⟨edge,h⟩
    exact excluded' edge.val (labels edge.val edge.property) ((S.mem_target b edge).mp h)
  have ne : a ≠ b := by
    intro eq
    have same : v = w := congrArg Subtype.val eq
    have ports := entry.symm.trans ((congrArg (Net.Expansion.host C L) same).trans entry')
    exact distinct (Port.input.inj (f.matchEmbedding.ports_injective_of_not_output
      (by simp [Port.IsOutput]) (by simp [Port.IsOutput]) ports))
  obtain ⟨rest,nd,boundary⟩ := S.two_input_order a b ne input input'
  exact ⟨S,labels,a,b,rest,entry,entry',nd,boundary,out⟩

end Hypernets.Copying.MaximalSharing

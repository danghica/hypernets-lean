import Hypernets.Copying.MaximalAtomComponent

/-! Retained primitive heads expose both original ordered argument wires. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.MaximalSharing
open Graph Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- A retained one-input/two-output primitive has exactly the same ordered
source and target ports in the original common context. -/
theorem binary_primitive_origin {e : (C.expand L).Edge} {p : Primitive} {a b c}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (source : (C.expand L).source e = [a]) (target : (C.expand L).target e = [b,c]) :
    ∃ v w x, C.edgeLabel e.1 = primitiveLabel d p ∧ C.source e.1 = [v] ∧ C.target e.1 = [w,x] ∧
      Net.Expansion.host C L v = a ∧ Net.Expansion.host C L w = b ∧ Net.Expansion.host C L x = c := by
  obtain ⟨copy⟩ := SharingRootOrigin.retained C cert trees label nonsharing
  have src : (C.source e.1).map (Net.Expansion.host C L) = [a] := by
    have h : (C.expand L).source e = (C.source e.1).map (Net.Expansion.host C L) := by
      rcases e with ⟨e,x⟩
      simpa only [copy.only x] using copy.source_eq
    exact h.symm.trans source
  have tgt : (C.target e.1).map (Net.Expansion.host C L) = [b,c] := by
    have h : (C.expand L).target e = (C.target e.1).map (Net.Expansion.host C L) := by
      rcases e with ⟨e,x⟩
      simpa only [copy.only x] using copy.target_eq
    exact h.symm.trans target
  have slen : (C.source e.1).length = 1 := by simpa using congrArg List.length src
  have tlen : (C.target e.1).length = 2 := by simpa using congrArg List.length tgt
  obtain ⟨v,sv⟩ := List.length_eq_one_iff.mp slen
  obtain ⟨w,x,tw⟩ : ∃ w x, C.target e.1 = [w,x] := by
    cases eq : C.target e.1 with
    | nil => simp [eq] at tlen
    | cons w rest =>
      have len : rest.length = 1 := by simpa [eq] using tlen
      obtain ⟨x,rfl⟩ := List.length_eq_one_iff.mp len
      exact ⟨w,x,rfl⟩
  refine ⟨v,w,x,?_,sv,tw,?_,?_,?_⟩
  · exact (copy.primitive p).mp (by change (L e.1).edgeLabel e.2 = _ at label; simpa only [copy.only e.2] using label)
  · simpa only [sv,List.map_cons,List.map_nil,List.cons.injEq,and_true] using src
  · exact (List.cons.inj (by simpa only [tw,List.map_cons,List.map_nil] using tgt)).1
  · exact (List.cons.inj (List.cons.inj (by simpa only [tw,List.map_cons,List.map_nil] using tgt)).2).1

end Hypernets.Copying.MaximalSharing

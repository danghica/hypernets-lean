import Hypernets.Copying.AssignmentMatch
import Hypernets.Copying.TargetSwapExpansion

/-! Canonical writes commute with renaming, plugging and simultaneous expansion. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment.Match
open Graph Combined

noncomputable def canonical_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    {v} (m : Match G v) : StateIso m.canonical (m.map (MatchEmbedding.ofDeepIso f)).canonical := by
  let n := m.map (MatchEmbedding.ofDeepIso f)
  let swap := TargetSwap.rename f m.newValue m.oldValue m.new_not_input m.old_not_input m.values_typed
    n.new_not_input n.old_not_input n.values_typed
  have eq : m.filler.reboundary (labelEquiv_input d (swap.edge_label m.headEdge))
      (labelEquiv_output d (swap.edge_label m.headEdge)) = n.filler := by
    unfold filler; rw [reboundary_comp]
  exact (Replacement.rename swap m.headEdge m.filler v).trans
    (StateIso.ofEq (congrArg (fun A => Replacement.state n.swapped n.headEdge A
      (Port.map f.vertices.toFun v)) eq))

noncomputable def canonical_plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    {G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole))}
    {v} (m : Match G v) :
    StateIso (m.map (MatchEmbedding.plug C hole G)).canonical (plugState C hole m.canonical) := by
  let n := m.map (MatchEmbedding.plug C hole G)
  let swap := DeepIso.ofIso (TargetSwap.plug C hole G m.newValue m.oldValue
    m.new_not_input m.old_not_input m.values_typed n.new_not_input n.old_not_input n.values_typed)
  have first : StateIso n.canonical
      (Replacement.state (C.plug hole m.swapped) (.inr m.headEdge) m.filler
        (Net.Replacement.insert C hole G v)) := by
    have h := Replacement.rename swap n.headEdge n.filler (Net.Replacement.insert C hole G v)
    simpa only [canonical,swapped,filler,n,map,MatchEmbedding.plug,MatchEmbedding.expand,swap,DeepIso.ofIso,Net.RelIso.ofIso,TargetSwap.plug,TargetSwap.expand,Bijection.refl,Port.map_id_fun,id_eq,Net.reboundary_refl] using h
  have second := Replacement.plug C hole m.swapped m.headEdge m.filler v
  have attached : Net.Replacement.insert C hole m.swapped v = Net.Replacement.insert C hole G v :=
    TargetSwap.insert_plug C hole G _ _ _ _ _ v
  rw [attached] at second
  exact first.trans second

/-- Expand a canonical write in one component, allowing an independently represented result. -/
noncomputable def canonical_expand_result {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e) {v w}
    (m : Match (F hole) v) (result : StateIso m.canonical ⟨K hole,(.search,w)⟩) :
    StateIso (m.map (MatchEmbedding.expand C F hole)).canonical
      ⟨C.expand K,(.search,Net.Expansion.insert C K hole w)⟩ := by
  let n := m.map (MatchEmbedding.expand C F hole)
  let P := TargetSwap.family C F hole m.newValue m.oldValue m.new_not_input m.old_not_input m.values_typed
  let swap := DeepIso.ofIso (TargetSwap.expand C F hole m.newValue m.oldValue
    m.new_not_input m.old_not_input m.values_typed n.new_not_input n.old_not_input n.values_typed)
  have first : StateIso n.canonical
      (Replacement.state (C.expand P) ⟨hole,m.headEdge⟩ m.filler (Net.Expansion.insert C F hole v)) := by
    have h := Replacement.rename swap n.headEdge n.filler (Net.Expansion.insert C F hole v)
    simpa only [canonical,swapped,filler,n,map,MatchEmbedding.plug,MatchEmbedding.expand,swap,DeepIso.ofIso,Net.RelIso.ofIso,TargetSwap.plug,TargetSwap.expand,Bijection.refl,Port.map_id_fun,id_eq,Net.reboundary_refl] using h
  let iso : DeepIso (P hole) m.swapped := {
    vertices := Bijection.refl _,edges := Bijection.refl _
    internal_label := fun _ => rfl
    edge_label := fun e => labelEquiv_refl d ((F hole).edgeLabel e)
    source := by intro e; simp only [Bijection.refl,Port.map_id_fun,List.map_id_fun]; rfl
    target := by
      intro e
      simp only [Bijection.refl,Port.map_id_fun,List.map_id_fun]
      change ((F hole).target e).map (TargetSwap.componentPermutation C F hole m.newValue m.oldValue hole).toFun = _
      simp [TargetSwap.componentPermutation,TargetSwap.permutation] }
  have component : StateIso (Replacement.state (P hole) m.headEdge m.filler v) ⟨K hole,(.search,w)⟩ := by
    have h := Replacement.rename iso m.headEdge m.filler v
    have eq : StateIso (Replacement.state (P hole) m.headEdge m.filler v) m.canonical := by
      simpa only [canonical,iso,Bijection.refl,Port.map_id_fun,id_eq,Net.reboundary_refl] using h
    exact eq.trans result
  have second := Replacement.expand_result C P K hole
    (fun e ne => (TargetSwap.family_other C F hole _ _ _ _ _ e ne).trans (others e ne))
    m.headEdge m.filler v w component
  have attached : Net.Expansion.insert C P hole v = Net.Expansion.insert C F hole v :=
    TargetSwap.insert_family C F hole _ _ _ _ _ hole v
  rw [attached] at second
  exact first.trans second
end Hypernets.Copying.Assignment.Match

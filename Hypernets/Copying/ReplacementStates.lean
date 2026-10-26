import Hypernets.Copying.SelectionExamples
import Hypernets.Graph.PlugUnits

/-! State-level congruences for a canonical one-edge replacement.
All token maps are tracked, including attachment at cyclic host boundaries. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph
namespace StateIso

/-- Transporting a vertex along graph equality transports the whole state. -/
theorem cast_state {d I O} {G H : Hypernet d I O} (eq : G = H)
    (mode : Focus) (v : G.Vertex) :
    (⟨H,(mode,cast (congrArg (fun G => G.Vertex) eq) v)⟩ : State d I O) = ⟨G,(mode,v)⟩ := by
  cases eq; rfl

/-- State isomorphism lifts through the actual shallow attachment map. -/
def plug {d I O} (C : Hypernet d I O) (e : C.Edge)
    {s t : State d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (f : StateIso s t) :
    StateIso (plugState C e s) (plugState C e t) where
  graph := Net.RelIso.plug C e (labelEquiv_refl d) f.graph
  mode := f.mode
  vertex := (Net.RelIsoPlug.map_insert C e f.graph s.2.2).trans
    (congrArg (Net.Replacement.insert C e t.1) f.vertex)

/-- Equality of graphs and coordinates supplies an isomorphism fixing the represented state. -/
def ofEq {d I O} {s t : State d I O} (eq : s = t) : StateIso s t := by
  cases eq; exact refl s

/-- Lift one changed component and its token through simultaneous assembly. -/
noncomputable def expand {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (others : ∀ b, b ≠ e → F b = K b) {v w} (f : StateIso ⟨F e,v⟩ ⟨K e,w⟩) :
    StateIso ⟨C.expand F,(v.1,Net.Expansion.insert C F e v.2)⟩
      ⟨C.expand K,(w.1,Net.Expansion.insert C K e w.2)⟩ := by
  classical
  let family : ∀ b, DeepIso (F b) (K b) := fun b => by
    by_cases eq : b = e
    · subst b; exact f.graph
    · rw [others b eq]; exact DeepIso.refl _
  have same : family e = f.graph := by simp [family]
  refine ⟨Net.ExpansionIso.iso C family,f.mode,?_⟩
  have commute := Net.ExpansionIso.map_insert C family e v.2
  rw [same] at commute
  exact commute.trans (congrArg (Net.Expansion.insert C K e) f.vertex)
end StateIso

/-- Equal-interface reindexing preserves the selected primitive head. -/
theorem head_reboundary {d I O J K} {G : Hypernet d I O} {v e p}
    (hi : I = J) (ho : O = K) (head : MatchEmbedding.HeadAt G v e p) :
    MatchEmbedding.HeadAt (G.reboundary hi ho) (Port.cast hi ho v) e p := by
  exact ⟨head.1,List.mem_map_of_mem head.2⟩

namespace Replacement
/-- Replace one edge and resume at the old token wire, retained by host inclusion. -/
noncomputable def state {d I O} (G : Hypernet d I O) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) (v : G.Vertex) : State d I O :=
  ⟨G.plug e A,(.search,Net.Replacement.host G e A v)⟩

/-- Nested replacement has the same successor as replacement inside the inserted component. -/
noncomputable def plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) (v : G.Vertex) :
    StateIso (state (C.plug hole G) (.inr e) A (Net.Replacement.insert C hole G v))
      (plugState C hole (state G e A v)) where
  graph := DeepIso.ofIso (C.plug_assoc hole G e A)
  mode := rfl
  vertex := Net.PlugAssoc.map_middle C hole G e A v

/-- A single replacement in an expansion can be regrouped into its selected filler. -/
noncomputable def expand {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (a : C.Edge) (e : (F a).Edge)
    (A : Hypernet d ((alphabet d).signature.input ((F a).edgeLabel e))
      ((alphabet d).signature.output ((F a).edgeLabel e))) (v : (F a).Vertex) :
    StateIso (state (C.expand F) ⟨a,e⟩ A (Net.Expansion.insert C F a v))
      ⟨C.expand (Net.ExpansionPlug.family C F a e A),
        (.search,Net.Expansion.insert C (Net.ExpansionPlug.family C F a e A) a
          (cast (congrArg (fun G => G.Vertex) (Net.ExpansionPlug.family_same C F a e A).symm)
            (Net.Replacement.host (F a) e A v)))⟩ where
  graph := DeepIso.ofIso (Net.ExpansionPlug.iso C F a e A)
  mode := rfl
  vertex := Net.ExpansionPlug.map_component C F a e A v

/-- Recursive renaming of the source transports canonical replacement and its old token. -/
noncomputable def rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H) (e : G.Edge)
    (A : Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e))) (v : G.Vertex) :
    StateIso (state G e A v)
      (state H (f.edges.toFun e)
        (A.reboundary (labelEquiv_input d (f.edge_label e)) (labelEquiv_output d (f.edge_label e)))
        (Port.map f.vertices.toFun v)) where
  graph := f.plugHost e (labelEquiv_input d (f.edge_label e)) (labelEquiv_output d (f.edge_label e))
    (labelEquiv_refl d) A
  mode := rfl
  vertex := Net.HostPlug.map_host f e _ _ A v
/-- Canonical replacement commutes with assembly even when the result filler
has an independently chosen recursively isomorphic representation. -/
noncomputable def expand_result {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (a : C.Edge)
    (others : ∀ b, b ≠ a → F b = K b) (e : (F a).Edge)
    (A : Hypernet d ((alphabet d).signature.input ((F a).edgeLabel e))
      ((alphabet d).signature.output ((F a).edgeLabel e))) (v : (F a).Vertex) (w : (K a).Vertex)
    (f : StateIso (state (F a) e A v) ⟨K a,(.search,w)⟩) :
    StateIso (state (C.expand F) ⟨a,e⟩ A (Net.Expansion.insert C F a v))
      ⟨C.expand K,(.search,Net.Expansion.insert C K a w)⟩ := by
  classical
  let P := Net.ExpansionPlug.family C F a e A
  have component : StateIso
      ⟨P a,(.search,cast (congrArg (fun G => G.Vertex)
        (Net.ExpansionPlug.family_same C F a e A).symm) (Net.Replacement.host (F a) e A v))⟩
      ⟨K a,(.search,w)⟩ :=
    (StateIso.ofEq (StateIso.cast_state (Net.ExpansionPlug.family_same C F a e A).symm _ _)).trans f
  exact (expand C F a e A v).trans (StateIso.expand C P K a
    (fun b ne => (Net.ExpansionPlug.family_other C F a e A b ne).trans (others b ne)) component)
end Replacement
end Hypernets.Copying.Combined

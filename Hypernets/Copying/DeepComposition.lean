import Hypernets.Copying.Contexts
import Hypernets.Graph.RelIsoPlug
import Hypernets.Graph.PlugAssociativity

/-! Nested copying-graph replacement associates up to recursive isomorphism.
The generic carrier proofs are shared with the preserved linear development. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Changing the same box to recursively isomorphic bodies preserves recursive
isomorphism of the surrounding graph. All outer names remain fixed. -/
noncomputable def replaceBox_deepIso {d I O} (G : Hypernet (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet d)) (label : G.edgeLabel e = .inr b)
    {H K : Hypernet d [.term] (environmentInterface (b.bound + b.freeVariables) b.freeAtoms)}
    (f : DeepIso H K) : DeepIso (replaceBox G e b label H) (replaceBox G e b label K) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label x := by
    classical
    by_cases eq : x = e
    · subst x
      simp only [replaceBox, Net.relabelEdges, Bijection.refl, id_eq, ↓reduceIte]
      exact BoxRelated.bodies ⟨f⟩
    · change LabelEquiv (d + 1)
        (if x = e then .inr ⟨b.bound, b.freeVariables, b.freeAtoms, H⟩ else G.edgeLabel x)
        (if x = e then .inr ⟨b.bound, b.freeVariables, b.freeAtoms, K⟩ else G.edgeLabel x)
      simp only [alphabet, nextAlphabet, ite_eq_right eq]
      exact labelEquiv_refl (d + 1) _
  source x := by change (G.source x).map (Port.map id) = G.source x; simp
  target x := by change (G.target x).map (Port.map id) = G.target x; simp

/-- Isomorphic replacements produce isomorphic results in every fixed addressed
context, including replacement inside any finite number of enclosing boxes. -/
noncomputable def plugAt_deepIso {depth I O} {G : Hypernet depth I O} {r J K}
    (site : Site G r J K) {H K' : Hypernet r J K} (f : DeepIso H K') :
    DeepIso (plugAt site H) (plugAt site K') := by
  induction site with
  | shallow C e => exact Net.RelIso.plug C e (labelEquiv_refl _) f
  | inside e b label inner ih => exact replaceBox_deepIso _ e b label (ih f)

/-- Replacing a selected box twice leaves precisely the last body. -/
theorem replaceBox_overwrite {d I O} (G : Hypernet (d + 1) I O)
    (e : G.Edge) (b : Box (alphabet d)) (label : G.edgeLabel e = .inr b)
    (A B : Hypernet d [.term] (environmentInterface (b.bound + b.freeVariables) b.freeAtoms))
    (label' : (replaceBox G e b label A).edgeLabel e = .inr ⟨b.bound, b.freeVariables, b.freeAtoms, A⟩) :
    replaceBox (replaceBox G e b label A) e ⟨b.bound, b.freeVariables, b.freeAtoms, A⟩ label' B =
      replaceBox G e b label B := by
  classical
  simp only [replaceBox, Net.relabelEdges]
  congr 1
  funext x
  by_cases h : x = e <;> simp [alphabet, nextAlphabet, h]

/-- Changing the body of an inserted box commutes with shallow insertion. -/
noncomputable def plug_replaceBox_iso {d I O} (C : Hypernet (d + 1) I O) (e : C.Edge)
    (H : Hypernet (d + 1) ((alphabet (d + 1)).signature.input (C.edgeLabel e))
      ((alphabet (d + 1)).signature.output (C.edgeLabel e)))
    (f : H.Edge) (b : Box (alphabet d)) (label : H.edgeLabel f = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound + b.freeVariables) b.freeAtoms)) :
    Net.Iso (replaceBox (C.plug e H) (.inr f) b label A)
      (C.plug e (replaceBox H f b label A)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label x := by
    classical
    cases x with
    | inl x => simp [replaceBox, Net.relabelEdges, Net.plug, Net.Replacement.edgeLabel, Bijection.refl]
    | inr x =>
      simp [Net.plug, Net.Replacement.edgeLabel, replaceBox, Net.relabelEdges, Bijection.refl]
  source x := by
    cases x with
    | inl x => simp [Net.plug, Net.Replacement.source, Bijection.refl, Net.Replacement.host]
    | inr x =>
      change ((H.source x).map (Net.Replacement.insert C e H)).map (Port.map id) =
        (H.source x).map (Net.Replacement.insert C e (replaceBox H f b label A))
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      dsimp only [Function.comp_def]
      rw [Port.map_id]
      cases v <;> rfl
  target x := by
    cases x with
    | inl x => simp [Net.plug, Net.Replacement.target, Bijection.refl, Net.Replacement.host]
    | inr x =>
      change ((H.target x).map (Net.Replacement.insert C e H)).map (Port.map id) =
        (H.target x).map (Net.Replacement.insert C e (replaceBox H f b label A))
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      dsimp only [Function.comp_def]
      rw [Port.map_id]
      cases v <;> rfl

/-- After inserting a graph at an outer site, locate an inner site of that graph
in the result. The address follows constructors directly, without choosing an isomorphism. -/
noncomputable def Site.comp {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) {H : Hypernet r J K} {q U V}
    (t : Site H q U V) : Site (plugAt s H) q U V := by
  classical
  induction s with
  | shallow C e =>
      cases t with
      | shallow H f => exact .shallow (C.plug e H) (.inr f)
      | inside f b label inner => exact .inside (G := C.plug e H) (.inr f) b label inner
  | inside e b label inner ih =>
      exact .inside (G := plugAt (.inside e b label inner) H) e ⟨b.bound, b.freeVariables, b.freeAtoms, plugAt inner H⟩
        (by simp [plugAt, replaceBox, Net.relabelEdges, alphabet, nextAlphabet]) (ih t)

/-- Arbitrary nested substitutions associate up to recursive isomorphism. -/
noncomputable def plugAt_assoc {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) {H : Hypernet r J K} {q U V}
    (t : Site H q U V) (A : Hypernet q U V) :
    DeepIso (plugAt (s.comp t) A) (plugAt s (plugAt t A)) := by
  induction s with
  | shallow C e =>
      cases t with
      | shallow H f => exact DeepIso.ofIso (C.plug_assoc e H f A)
      | inside f b label inner => exact DeepIso.ofIso (plug_replaceBox_iso C e _ f b label (plugAt inner A))
  | inside e b label inner ih =>
      change DeepIso (replaceBox (replaceBox _ e b label (plugAt inner H)) e
        ⟨b.bound, b.freeVariables, b.freeAtoms, plugAt inner H⟩
        (by simp [alphabet, nextAlphabet]) (plugAt (inner.comp t) A)) _
      rw [replaceBox_overwrite]
      exact replaceBox_deepIso _ e b label (ih t)



/-- Composition of two certified single-hole contexts still has exactly the
selected inner hole. All retained outer labels stay hole-free. -/
theorem SoleHole.comp {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) {H : Hypernet r J K} {q U V}
    (t : Site H q U V) (ss : SoleHole s) (ts : SoleHole t) :
    SoleHole (s.comp t) := by
  induction s with
  | shallow C e =>
    cases t with
    | shallow H f =>
      refine ⟨ts.1,?_⟩
      intro x ne
      cases x with
      | inl x => exact ss.2 x.val x.property
      | inr x => exact ts.2 x (fun eq => ne (congrArg Sum.inr eq))
    | inside f b label inner =>
      refine ⟨ts.1,?_⟩
      intro x ne
      cases x with
      | inl x => exact ss.2 x.val x.property
      | inr x => exact ts.2 x (fun eq => ne (congrArg Sum.inr eq))
  | @inside d I O G e b label r J K inner ih =>
    refine ⟨ih t ss.1 ts,?_⟩
    intro x ne
    simpa [plugAt,replaceBox,ne] using ss.2 x ne

/-- Full graph-context closure: the composed address is unique and its host
is binding-free. The inner hole's interface need not be closed. -/
theorem context_comp_certified {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) {H : Hypernet r J K} {q U V}
    (t : Site H q U V) (ss : SoleHole s) (ts : SoleHole t)
    (source : J ≠ []) (gf : BindingFree G) (hf : BindingFree H) :
    SoleHole (s.comp t) ∧ BindingFree (plugAt s H) :=
  ⟨SoleHole.comp s t ss ts,BindingFree.plugAt s H (SoleHole.sourced s ss source) gf hf⟩

end Hypernets.Copying

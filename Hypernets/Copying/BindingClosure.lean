import Hypernets.Copying.BindingFree

/-! The path argument behind plugging closure (Appendix E).
The replaced hole has a source, as do all translated term holes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph
open Graph.Net.Replacement

variable {d I O} (C : Hypernet d I O) (h : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel h))
      ((alphabet d).signature.output (C.edgeLabel h)))

theorem adjacent_host_insert (e : {e : C.Edge // e ≠ h}) (f : H.Edge)
    (a : (C.plug h H).Adjacent (.inl e) (.inr f)) : C.Adjacent e.val h := by
  obtain ⟨v,hv,hw⟩ := a
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hw
  obtain ⟨i,_,hi⟩ := insert_source_host C h H (H.source_not_output hy) eq
  exact ⟨x,hx,hi ▸ C.sourcePort_mem h i⟩

theorem adjacent_insert_host (e : H.Edge) (f : {e : C.Edge // e ≠ h})
    (a : (C.plug h H).Adjacent (.inr e) (.inl f)) : C.Adjacent h f.val := by
  obtain ⟨v,hv,hw⟩ := a
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hw
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hv
  obtain ⟨i,_,hi⟩ := insert_target_host C h H (H.target_not_input hy) eq
  exact ⟨x,hi ▸ C.targetPort_mem h i,hx⟩

/-- A suffix reaching a surviving hole either traces back entirely inside the
inserted graph, or traces back to a host hole (possibly the replaced one).
An inserted-to-host crossing would give a forbidden path from the old hole. -/
theorem ancestor_origin
    (free : ShallowBindingFree C) (hole : HoleLabel d (C.edgeLabel h))
    (source : ∃ v, v ∈ C.source h)
    {e f : (C.plug h H).Edge} (path : Ancestor (C.plug h H) e f)
    (lastHole : HoleLabel d ((C.plug h H).edgeLabel f)) :
    match e with
    | .inl e => ∃ b, HoleLabel d (C.edgeLabel b) ∧ Ancestor C e.val b
    | .inr e => ∃ b, HoleLabel d (H.edgeLabel b) ∧ Ancestor H e b := by
  induction path with
  | refl e =>
    cases e with
    | inl e => exact ⟨e.val,lastHole,.refl _⟩
    | inr e => exact ⟨e,lastHole,.refl _⟩
  | @step e f g a p ih =>
    have ih := ih lastHole
    cases e with
    | inl e =>
      cases f with
      | inl f =>
        obtain ⟨b,bh,q⟩ := ih
        exact ⟨b,bh,.step ((adjacent_host_iff C h H e f).mp a) q⟩
      | inr f => exact ⟨h,hole,.step (adjacent_host_insert C h H e f a) (.refl h)⟩
    | inr e =>
      cases f with
      | inl f =>
        obtain ⟨b,bh,q⟩ := ih
        exact False.elim (free h b (hole_binding d hole) source bh
          ⟨f.val,adjacent_insert_host C h H e f a,q⟩)
      | inr f =>
        obtain ⟨b,bh,q⟩ := ih
        exact ⟨b,bh,.step ((adjacent_insert_iff C h H
          (hole_nonSelfLoop free h hole) e f).mp a) q⟩

/-- Shallow binding-freedom is closed under replacing a hole with at least one
source. The proof retains zero-input holes elsewhere and does not collapse
positive paths to reflexive reachability. -/
theorem shallow_plug
    (cf : ShallowBindingFree C) (hf : ShallowBindingFree H)
    (hole : HoleLabel d (C.edgeLabel h)) (source : ∃ v, v ∈ C.source h) :
    ShallowBindingFree (C.plug h H) := by
  intro e f bad src fh path
  obtain ⟨g,a,p⟩ := path
  have origin := ancestor_origin C h H cf hole source p fh
  cases e with
  | inl e =>
    have es : ∃ v, v ∈ C.source e.val := by
      obtain ⟨v,hv⟩ := src
      obtain ⟨x,hx,_⟩ := List.mem_map.mp hv
      exact ⟨x,hx⟩
    cases g with
    | inl g =>
      obtain ⟨b,bh,q⟩ := origin
      exact cf e.val b bad es bh ⟨g.val,(adjacent_host_iff C h H e g).mp a,q⟩
    | inr g =>
      exact cf e.val h bad es hole ⟨h,adjacent_host_insert C h H e g a,.refl h⟩
  | inr e =>
    have es : ∃ v, v ∈ H.source e := by
      obtain ⟨v,hv⟩ := src
      obtain ⟨x,hx,_⟩ := List.mem_map.mp hv
      exact ⟨x,hx⟩
    cases g with
    | inl g =>
      obtain ⟨b,bh,q⟩ := origin
      exact cf h b (hole_binding d hole) source bh
        ⟨g.val,adjacent_insert_host C h H e g a,q⟩
    | inr g =>
      obtain ⟨b,bh,q⟩ := origin
      exact hf e b bad es bh ⟨g,(adjacent_insert_iff C h H
        (hole_nonSelfLoop cf h hole) e g).mp a,q⟩


/-- Precisely those addressed replacements that replace a sourced hole.
Translated term holes always satisfy this condition. -/
def SourcedHole {d I O} {G : Hypernet d I O} {r J K} (s : Site G r J K) : Prop := by
  induction s with
  | shallow C e => exact HoleLabel _ (C.edgeLabel e) ∧ ∃ v, v ∈ C.source e
  | inside _ _ _ _ ih => exact ih

theorem paths_shallow {d I O} (C : Hypernet d I O) (h : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel h))
      ((alphabet d).signature.output (C.edgeLabel h)))
    (cf : BindingPaths d C) (hf : BindingPaths d H)
    (hole : HoleLabel d (C.edgeLabel h)) (source : ∃ v, v ∈ C.source h) :
    BindingPaths d (C.plug h H) := by
  cases d with
  | zero => exact shallow_plug C h H cf hf hole source
  | succ d =>
    refine ⟨shallow_plug C h H cf.1 hf.1 hole source,?_⟩
    intro e
    cases e with
    | inl e => exact cf.2 e.val
    | inr e => exact hf.2 e

theorem shallow_replaceBox {d I O} (G : Hypernet (d+1) I O)
    (e : G.Edge) (b : Box (alphabet d)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms))
    (free : ShallowBindingFree G) : ShallowBindingFree (replaceBox G e b label body) := by
  classical
  apply shallow_of_map (G := replaceBox G e b label body) (H := G) id (fun h => h) ?_ (fun _ h => h) ?_ free
  · intro f hf
    by_cases eq : f = e
    · subst f
      simp [label,BindingLabel]
    · simpa [replaceBox,eq] using hf
  · intro f hf
    by_cases eq : f = e
    · subst f
      simp [HoleLabel,primitiveLabel] at hf
    · simpa [replaceBox,eq] using hf

/-- Recursive Appendix-E closure for sourced hole occurrences, including holes
under arbitrarily many boxes. Paths never cross a box boundary. -/
theorem paths_plugAt {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) (H : Hypernet r J K)
    (hole : SourcedHole s) (gf : BindingPaths d G) (hf : BindingPaths r H) :
    BindingPaths d (plugAt s H) := by
  induction s with
  | shallow C e => exact paths_shallow C e H gf hf hole.1 hole.2
  | @inside d I O G e b label r J K s ih =>
    have bf : BindingPaths d b.body := by simpa [label] using gf.2 e
    refine ⟨shallow_replaceBox G e b label _ gf.1,?_⟩
    intro f
    classical
    change (match (if f = e then
      .inr (⟨b.bound,b.freeVariables,b.freeAtoms,plugAt s H⟩ : Box (alphabet d))
      else G.edgeLabel f) with
      | .inl _ => True
      | .inr b => BindingPaths d b.body)
    by_cases eq : f = e
    · simp only [eq,ite_true]
      exact ih H hole bf hf
    · simp only [eq,ite_false]
      cases lab : G.edgeLabel f with
      | inl p => trivial
      | inr b => simpa [lab] using gf.2 f

theorem plugAt {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) (H : Hypernet r J K)
    (hole : SourcedHole s) (gf : BindingFree G) (hf : BindingFree H) :
    BindingFree (Copying.plugAt s H) :=
  ⟨focusFree_closed s H gf.1 hf.1,paths_plugAt s H hole gf.2 hf.2⟩

end Hypernets.Copying.BindingFree

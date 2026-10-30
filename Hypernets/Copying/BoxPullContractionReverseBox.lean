import Hypernets.Copying.BoxPullContractionReverseBarrier
import Hypernets.Copying.BoxPullContractionNormalization
import Hypernets.Copying.PrimitiveContextOccurrence
import Hypernets.Copying.DerivationFillings

/-! Actual left boxes at sourced thunk interfaces. Only selected ports are
reflected; the new right contraction vertices have no global projection. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseBox
open Graph Opening Search.Expansion

/-- A closed corolla accepting a thunk is a box; the original alphabet has
no other nonhole label accepting that wire. Its actual whole body is retained. -/
theorem box_at_input {d J K} {G : Hypernet (d+1) J K} {a}
    (c : LabelCopy G a) (closed : HoleFree G) (i : Fin J.length) (n : Nat)
    (typed : J[i] = .thunk n) :
    ∃ k h, ∃ B : Hypernet d [.term] (environmentInterface (n+k) h),
      ∃ g : Occurrence (box (bound := n) (freeVariables := k) B) G,
        g.ports (.input 0) = .input i := by
  cases a with
  | inl p =>
    have nohole : ∀ h, p ≠ .hole h := by
      intro h eq
      have no := closed c.edge
      rw [c.edge_label,eq] at no
      exact no h rfl
    have member : Wire.thunk n ∈ primitiveSignature.input p := by
      have member := List.getElem_mem (n := i.val) (l := J) i.isLt
      change J[i] ∈ J at member
      rw [typed] at member
      rw [← c.input] at member
      exact member
    exact False.elim (primitive_input_not_thunk p nohole n member)
  | inr b =>
    have inputs : [.thunk b.bound] = J := c.input
    have length : J.length = 1 := by rw [← inputs]; rfl
    have only : ∀ j : Fin J.length, j = i := by
      intro j; apply Fin.ext; have := j.isLt; have := i.isLt; omega
    have type : J[i] = .thunk b.bound := by
      have mem := List.getElem_mem (n := i.val) (l := J) i.isLt
      have singleton : ∀ v, v ∈ J → v = .thunk b.bound := by
        intro v hv
        rw [← inputs] at hv
        exact List.mem_singleton.mp hv
      exact singleton J[i] mem
    have bound : b.bound = n := Wire.thunk.inj (type.symm.trans typed)
    rcases b with ⟨bound',k,h,B⟩
    dsimp only at bound
    subst bound'
    let g : Occurrence (box (bound := n) (freeVariables := k) B) G :=
      Occurrence.labelledCorolla G c.edge _ c.edge_label
    refine ⟨k,h,B,g,?_⟩
    have range : List.finRange J.length = [i] := by
      apply List.ext_getElem
      · simpa using length
      · intro j hj hk
        have zero : j = 0 := by simp at hk; omega
        subst j
        simp only [List.getElem_finRange,List.getElem_cons_zero]
        exact only _
    have source := g.source (0 : Fin 1)
    rw [Occurrence.labelledCorolla_edges,c.source,range] at source
    exact (List.cons.inj source).1

variable {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand R))
include cert closed

/-- At each actual original thunk input, the left filling has a complete box
occurrence with the same binding arity. The free interface is reconstructed
from the original left corolla, rather than guessed from the right box. -/
theorem left_at_input (e : C.Edge)
    (i : Fin ((alphabet (d+1)).signature.input (C.edgeLabel e)).length) (n : Nat)
    (typed : ((alphabet (d+1)).signature.input (C.edgeLabel e))[i] = .thunk n) :
    ∃ k h, ∃ B : Hypernet d [.term] (environmentInterface (n+k) h),
      ∃ g : Occurrence (box (bound := n) (freeVariables := k) B) (C.expand L),
        g.ports (.input 0) = Net.Expansion.host C L (C.sourcePort e i) := by
  have lc : HoleFree (C.expand L) :=
    ((DeepFilling.expand C L R cert).allLabels_iff (T := template) _ (fun pair => UpToIso.allLabels _ pair)).mpr closed
  obtain ⟨k,h,B,g,input⟩ := box_at_input (leftCopy (cert e)).2 (fun a => lc ⟨e,a⟩) i n typed
  exact ⟨k,h,B,g.comp (Occurrence.expand C L e),congrArg (Net.Expansion.insert C L e) input⟩

/-- An actual right box attached to an original thunk port therefore has a
complete left box at the corresponding original port. -/
theorem reflectBox {n k h} (B : Hypernet d [.term] (environmentInterface (n+k) h))
    (f : Occurrence (box (bound := n) (freeVariables := k) B) (C.expand R))
    {q : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R q) :
    ∃ k' h', ∃ A : Hypernet d [.term] (environmentInterface (n+k') h'),
      ∃ g : Occurrence (box (bound := n) (freeVariables := k') A) (C.expand L),
        g.ports (.input 0) = Net.Expansion.host C L q := by
  let e := f.edges (0 : Fin 1)
  have source : Net.Expansion.host C R q ∈ (C.expand R).source e := by
    rw [← attached,← f.source (0 : Fin 1)]
    exact List.mem_cons_self
  obtain ⟨v,mem,eq⟩ := List.mem_map.mp source
  cases v with
  | internal x => exact False.elim (Net.Expansion.host_ne_internal C R q e.1 x eq.symm)
  | output j => exact False.elim ((R e.1).source_not_output mem trivial)
  | input i =>
    have port : C.sourcePort e.1 i = q := Net.Expansion.host_injective C R eq
    have ty := f.matchEmbedding.vertexLabel f.label (.input 0)
    change (C.expand R).vertexLabel (f.ports (.input 0)) = .thunk n at ty
    rw [attached] at ty
    have ty : C.vertexLabel q = .thunk n := (Net.Expansion.host_label C R q).symm.trans ty
    have typed : ((alphabet (d+1)).signature.input (C.edgeLabel e.1))[i] = .thunk n :=
      (C.sourcePort_label e.1 i).symm.trans (port.symm ▸ ty)
    obtain ⟨k',h',A,g,input⟩ := left_at_input C cert closed e.1 i n typed
    exact ⟨k',h',A,g,input.trans (congrArg (Net.Expansion.host C L) port)⟩
end Hypernets.Copying.BoxPullContraction.ReverseBox

import Hypernets.Copying.ReadStub

/-! State-level transport for typed target exchange. Tokens are preserved, not exchanged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TargetSwap
open Graph Combined

/-- Non-input ports remain non-inputs under incidence-preserving occurrence maps. -/
theorem embedded_not_input {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v} (nv : ¬ v.IsInput) : ¬ (f.ports v).IsInput := by
  obtain ⟨e,he⟩ := (G.target_coverage v).mpr nv
  exact H.target_not_input (f.target_mem he)

noncomputable def state {d I O} (G : Hypernet d I O) (a b : G.Vertex)
    (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (typed : G.vertexLabel a = G.vertexLabel b)
    (v : G.Vertex) : Combined.State d I O := ⟨net G a b na nb typed,(.search,v)⟩

/-- Graph equality transports the non-input side condition of an exchanged endpoint. -/
theorem cast_not_input {d I O} {G H : Hypernet d I O} (eq : G = H) {v : G.Vertex}
    (nv : ¬ v.IsInput) : ¬ (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) v).IsInput := by
  cases eq; exact nv

theorem cast_typed {d I O} {G H : Hypernet d I O} (eq : G = H) {a b : G.Vertex}
    (typed : G.vertexLabel a = G.vertexLabel b) :
    H.vertexLabel (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) a) =
      H.vertexLabel (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) b) := by
  cases eq; exact typed

noncomputable def state_cast {d I O} {G H : Hypernet d I O} (eq : G = H)
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (typed : G.vertexLabel a = G.vertexLabel b)
    (v : G.Vertex) :
    StateIso (state H (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) a)
      (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) b) (cast_not_input eq na) (cast_not_input eq nb)
      (cast_typed eq typed) (cast (congrArg (fun (G : Hypernet d I O) => G.Vertex) eq) v)) (state G a b na nb typed v) := by
  cases eq; exact StateIso.refl _

/-- A state comparison also tracks the two endpoints which are to be exchanged. -/
noncomputable def state_congr {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (typed : G.vertexLabel a = G.vertexLabel b)
    (a' b' : H.Vertex) (na' : ¬ a'.IsInput) (nb' : ¬ b'.IsInput) (typed' : H.vertexLabel a' = H.vertexLabel b')
    (ha : Port.map f.vertices.toFun a = a') (hb : Port.map f.vertices.toFun b = b')
    (v : G.Vertex) (w : H.Vertex) (token : Port.map f.vertices.toFun v = w) :
    StateIso (state G a b na nb typed v) (state H a' b' na' nb' typed' w) := by
  subst a'; subst b'
  exact ⟨rename f a b na nb typed na' nb' typed',rfl,token⟩

/-- Target exchange inside a plugged state commutes with the original boundary attachment. -/
noncomputable def state_plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole)))
    (a b : G.Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (typed : G.vertexLabel a = G.vertexLabel b)
    (na' : ¬ (Net.Replacement.insert C hole G a).IsInput)
    (nb' : ¬ (Net.Replacement.insert C hole G b).IsInput)
    (typed' : (C.plug hole G).vertexLabel (Net.Replacement.insert C hole G a) =
      (C.plug hole G).vertexLabel (Net.Replacement.insert C hole G b)) (v : G.Vertex) :
    StateIso (state (C.plug hole G) (Net.Replacement.insert C hole G a)
      (Net.Replacement.insert C hole G b) na' nb' typed' (Net.Replacement.insert C hole G v))
      (plugState C hole (state G a b na nb typed v)) := by
  refine ⟨DeepIso.ofIso (plug C hole G a b na nb typed na' nb' typed'),rfl,?_⟩
  simpa only [DeepIso.ofIso,Net.RelIso.ofIso,plug,Bijection.refl,Port.map_id,state,plugState] using
    (insert_plug C hole G a b na nb typed v).symm

/-- Exchange commutes with expansion when the selected component has an independently
represented successor. The other components may contain arbitrary boxes and cycles. -/
noncomputable def state_expand_result {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e)) ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e)
    (a b : (F hole).Vertex) (na : ¬ a.IsInput) (nb : ¬ b.IsInput)
    (typed : (F hole).vertexLabel a = (F hole).vertexLabel b)
    (na' : ¬ (Net.Expansion.insert C F hole a).IsInput)
    (nb' : ¬ (Net.Expansion.insert C F hole b).IsInput)
    (typed' : (C.expand F).vertexLabel (Net.Expansion.insert C F hole a) =
      (C.expand F).vertexLabel (Net.Expansion.insert C F hole b)) {v w}
    (result : StateIso (state (F hole) a b na nb typed v) ⟨K hole,(.search,w)⟩) :
    StateIso (state (C.expand F) (Net.Expansion.insert C F hole a)
      (Net.Expansion.insert C F hole b) na' nb' typed' (Net.Expansion.insert C F hole v))
      ⟨C.expand K,(.search,Net.Expansion.insert C K hole w)⟩ := by
  let P := family C F hole a b na nb typed
  let first : StateIso (state (C.expand F) (Net.Expansion.insert C F hole a)
      (Net.Expansion.insert C F hole b) na' nb' typed' (Net.Expansion.insert C F hole v))
      ⟨C.expand P,(.search,Net.Expansion.insert C P hole v)⟩ := {
    graph := DeepIso.ofIso (expand C F hole a b na nb typed na' nb' typed')
    mode := rfl
    vertex := by
      simpa only [DeepIso.ofIso,Net.RelIso.ofIso,expand,Bijection.refl,Port.map_id,state,P] using
        (insert_family C F hole a b na nb typed hole v).symm }
  have component : StateIso ⟨P hole,(.search,v)⟩ ⟨K hole,(.search,w)⟩ := by
    have eq : (⟨P hole,(.search,v)⟩ : Combined.State _ _ _) = state (F hole) a b na nb typed v := by
      simp [P,family,componentPermutation,net,state]
    exact (StateIso.ofEq eq).trans result
  exact first.trans (StateIso.expand C P K hole
    (fun e ne => (family_other C F hole a b na nb typed e ne).trans (others e ne)) component)
end Hypernets.Copying.TargetSwap

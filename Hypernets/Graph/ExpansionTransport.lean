import Hypernets.Graph.ParallelExpansion
import Hypernets.Graph.ExpansionAssociativity
import Hypernets.Graph.TransportPlug

/-! Simultaneous expansion under a renamed or relabelled skeleton. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Graph
namespace Bijection
/-- Build inverse data from proved injectivity and surjectivity. -/
noncomputable def ofBijective {A B : Type} (f : A → B) (inj : Function.Injective f)
    (surj : ∀ b, ∃ a, f a = b) : Bijection A B where
  toFun := f
  invFun b := Classical.choose (surj b)
  left_inv a := inj (Classical.choose_spec (surj (f a)))
  right_inv b := Classical.choose_spec (surj b)

/-- Relabel component tags while applying a bijection in each dependent fibre. -/
noncomputable def sigmaMap {A B : Type} {X : A → Type} {Y : B → Type}
    (tags : Bijection A B) (fibres : ∀ a, Bijection (X a) (Y (tags.toFun a))) :
    Bijection (Σ a, X a) (Σ b, Y b) :=
  ofBijective (fun x => ⟨tags.toFun x.1,(fibres x.1).toFun x.2⟩)
    (by
      rintro ⟨a,x⟩ ⟨b,y⟩ eq
      have ab : a = b := tags.injective (congrArg Sigma.fst eq)
      subst b
      exact congrArg (Sigma.mk a) ((fibres a).injective (eq_of_heq (Sigma.mk.inj eq).2)))
    (by
      rintro ⟨b,y⟩
      obtain ⟨a,rfl⟩ : ∃ a, tags.toFun a = b := ⟨tags.invFun b,tags.right_inv b⟩
      exact ⟨⟨a,(fibres a).invFun y⟩,congrArg (Sigma.mk _) ((fibres a).right_inv y)⟩)
end Bijection

namespace Net.ExpansionTransport
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    {R S : Op → Op → Prop} {C D : Net σ I O} (f : RelIso R C D)
    (hi : ∀ e, σ.input (C.edgeLabel e) = σ.input (D.edgeLabel (f.edges.toFun e)))
    (ho : ∀ e, σ.output (C.edgeLabel e) = σ.output (D.edgeLabel (f.edges.toFun e)))
    (F : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))
    (K : (e : D.Edge) → Net σ (σ.input (D.edgeLabel e)) (σ.output (D.edgeLabel e)))
    (g : ∀ e, RelIso S ((F e).reboundary (hi e) (ho e)) (K (f.edges.toFun e)))

noncomputable def vertices : Bijection (C.expand F).Internal (D.expand K).Internal :=
  f.vertices.sum (Bijection.sigmaMap f.edges (fun e => (g e).vertices))

noncomputable def edges : Bijection (C.expand F).Edge (D.expand K).Edge :=
  Bijection.sigmaMap f.edges (fun e => (g e).edges)

theorem map_host (v : C.Vertex) :
    Port.map (vertices f hi ho F K g).toFun (Expansion.host C F v) =
      Expansion.host D K (Port.map f.vertices.toFun v) := by cases v <;> rfl

/-- Ordered source and target attachments commute with both levels of renaming. -/
theorem map_insert (e : C.Edge) (v : (F e).Vertex) :
    Port.map (vertices f hi ho F K g).toFun (Expansion.insert C F e v) =
      Expansion.insert D K (f.edges.toFun e)
        (Port.map (g e).vertices.toFun (Port.cast (hi e) (ho e) v)) := by
  cases v with
  | internal v => rfl
  | input i =>
    change Port.map _ (Expansion.host C F (C.sourcePort e i)) =
      Expansion.host D K (D.sourcePort (f.edges.toFun e) _)
    rw [map_host,f.sourcePort e (hi e)]
  | output i =>
    change Port.map _ (Expansion.host C F (C.targetPort e i)) =
      Expansion.host D K (D.targetPort (f.edges.toFun e) _)
    rw [map_host,f.targetPort e (ho e)]

/-- A skeleton isomorphism and independently represented components give a
whole-expansion isomorphism. Skeleton labels need only have matching interfaces. -/
noncomputable def iso : RelIso S (C.expand F) (D.expand K) where
  vertices := vertices f hi ho F K g
  edges := edges f hi ho F K g
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · exact f.internal_label v
    · exact (g e).internal_label v
  edge_label e := (g e.1).edge_label e.2
  source e := by
    obtain ⟨e,x⟩ := e
    change (((F e).source x).map (Expansion.insert C F e)).map _ =
      ((K (f.edges.toFun e)).source ((g e).edges.toFun x)).map _
    rw [← (g e).source]
    change _ = ((((F e).source x).map (Port.cast (hi e) (ho e))).map (Port.map (g e).vertices.toFun)).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert f hi ho F K g e v)
  target e := by
    obtain ⟨e,x⟩ := e
    change (((F e).target x).map (Expansion.insert C F e)).map _ =
      ((K (f.edges.toFun e)).target ((g e).edges.toFun x)).map _
    rw [← (g e).target]
    change _ = ((((F e).target x).map (Port.cast (hi e) (ho e))).map (Port.map (g e).vertices.toFun)).map _
    simp only [List.map_map]
    exact List.map_congr_left (fun v _ => map_insert f hi ho F K g e v)
end Net.ExpansionTransport
end Hypernets.Graph

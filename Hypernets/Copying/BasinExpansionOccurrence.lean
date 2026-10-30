import Hypernets.Copying.SharingBasin

/-! The selected common sharing context expands to a complete occurrence in
each original expanded host, retaining all local labels and attachment ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BasinExpansion
open Graph Opening
variable {d I O} {G : Hypernet d I O} {s : ShareSort} (S : G.RootedBasin s.wire)
    (labels : ∀ e, S.chosen e → SharingBasin.Eligible G s e)
    (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)
    (F : (e : G.Edge) → Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)))

noncomputable abbrev context := (SharingBasin.context S labels inputs distinct boundary).net
noncomputable abbrev base := SharingBasin.occurrence S labels inputs distinct boundary
abbrev family (e : S.Edge) := F e.val

noncomputable def ports : ((context S labels inputs distinct boundary).expand (family S F)).Vertex → (G.expand F).Vertex
  | .internal (.inl x) => .internal (.inl ((base S labels inputs distinct boundary).internals x))
  | .internal (.inr ⟨e,x⟩) => .internal (.inr ⟨e.val,x⟩)
  | .input i => Net.Expansion.host G F ((base S labels inputs distinct boundary).ports (.input i))
  | .output i => Net.Expansion.host G F ((base S labels inputs distinct boundary).ports (.output i))

theorem host (v : (context S labels inputs distinct boundary).Vertex) :
    ports S labels inputs distinct boundary F (Net.Expansion.host (context S labels inputs distinct boundary) (family S F) v) =
      Net.Expansion.host G F ((base S labels inputs distinct boundary).ports v) := by
  cases v with
  | internal x => rw [(base S labels inputs distinct boundary).internal_map]; rfl
  | input i => rfl
  | output i => rfl

theorem sourcePort (e : S.Edge)
    (i : Fin ((alphabet d).signature.input (G.edgeLabel e.val)).length) :
    (base S labels inputs distinct boundary).ports ((context S labels inputs distinct boundary).sourcePort e i) =
      G.sourcePort e.val i := by
  have row : ((context S labels inputs distinct boundary).source e).map
      (base S labels inputs distinct boundary).ports = G.source e.val :=
    (base S labels inputs distinct boundary).source e
  have eq := congrArg (fun xs => xs[i.val]?) row
  simp only [List.getElem?_map] at eq
  rw [List.getElem?_eq_getElem (by rw [(context S labels inputs distinct boundary).source_length]; exact i.isLt),
    List.getElem?_eq_getElem (by rw [G.source_length]; exact i.isLt)] at eq
  exact Option.some.inj eq

theorem targetPort (e : S.Edge)
    (i : Fin ((alphabet d).signature.output (G.edgeLabel e.val)).length) :
    (base S labels inputs distinct boundary).ports ((context S labels inputs distinct boundary).targetPort e i) =
      G.targetPort e.val i := by
  have row : ((context S labels inputs distinct boundary).target e).map
      (base S labels inputs distinct boundary).ports = G.target e.val :=
    (base S labels inputs distinct boundary).target e
  have eq := congrArg (fun xs => xs[i.val]?) row
  simp only [List.getElem?_map] at eq
  rw [List.getElem?_eq_getElem (by rw [(context S labels inputs distinct boundary).target_length]; exact i.isLt),
    List.getElem?_eq_getElem (by rw [G.target_length]; exact i.isLt)] at eq
  exact Option.some.inj eq

theorem insert (e : S.Edge) (v : (F e.val).Vertex) :
    ports S labels inputs distinct boundary F (Net.Expansion.insert (context S labels inputs distinct boundary) (family S F) e v) =
      Net.Expansion.insert G F e.val v := by
  cases v with
  | internal x => rfl
  | input i =>
    change ports S labels inputs distinct boundary F (Net.Expansion.host _ _ _) = Net.Expansion.host _ _ _
    rw [host,sourcePort]
  | output i =>
    change ports S labels inputs distinct boundary F (Net.Expansion.host _ _ _) = Net.Expansion.host _ _ _
    rw [host,targetPort]

/-- Expanding the original selected context preserves its full-label match. -/
noncomputable def occurrence : Occurrence
    ((context S labels inputs distinct boundary).expand (family S F)) (G.expand F) :=
  (show MatchEmbedding ((context S labels inputs distinct boundary).expand (family S F)) (G.expand F) from {
    ports := ports S labels inputs distinct boundary F
    edges e := ⟨e.1.val,e.2⟩
    edge_injective := by
      rintro ⟨e,x⟩ ⟨f,y⟩ eq
      have same : e = f := Subtype.ext (congrArg Sigma.fst eq)
      subst f
      have xy : x = y := eq_of_heq (Sigma.mk.inj eq).2
      subst y
      rfl
    primitive := fun _ _ h => h
    source := by
      intro e
      change (((F e.1.val).source e.2).map (Net.Expansion.insert (context S labels inputs distinct boundary) (family S F) e.1)).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => insert S labels inputs distinct boundary F e.1 v)
    target := by
      intro e
      change (((F e.1.val).target e.2).map (Net.Expansion.insert (context S labels inputs distinct boundary) (family S F) e.1)).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => insert S labels inputs distinct boundary F e.1 v)
  }).occurrence (fun _ => labelEquiv_refl _ _)

theorem occurrence_host (v : (context S labels inputs distinct boundary).Vertex) :
    (occurrence S labels inputs distinct boundary F).ports (Net.Expansion.host _ (family S F) v) =
      Net.Expansion.host G F ((base S labels inputs distinct boundary).ports v) :=
  host S labels inputs distinct boundary F v

end Hypernets.Copying.BasinExpansion

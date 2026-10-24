import Hypernets.Graph.ExpansionSearch

/-! Commuting general focus erasure with simultaneous expansion. -/
namespace Hypernets.Linear.ExpansionErasure
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}
    (C : Hypernet ops d I [])
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (f : Focussed C) (copy : ExpansionPaths.CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e))
    (t : C.Internal) (ht : f.target = .internal t)

noncomputable abbrev erased := FocusErasure.erase f t ht
abbrev focus := ExpansionPaths.focussed C H f copy free
noncomputable abbrev erasedExpansion := FocusErasure.erase (focus C H f copy free) (.inl t)
  (congrArg (Net.Expansion.host C H) ht)

def family (e : (erased C f t ht).Edge) :
    Hypernet ops d ((alphabet ops d).signature.input ((erased C f t ht).edgeLabel e))
      ((alphabet ops d).signature.output ((erased C f t ht).edgeLabel e)) := H e.val

/-- Delete the original focus target and discard the empty interior of its copy. -/
noncomputable def vertices : Bijection (erasedExpansion C H f copy free t ht).Internal
    ((erased C f t ht).expand (family C H f t ht)).Internal where
  toFun x := match x with
    | ⟨.inl v,ne⟩ => .inl ⟨v,fun eq => ne (congrArg Sum.inl eq)⟩
    | ⟨.inr ⟨e,v⟩,_⟩ => by
        classical
        by_cases eq : e = f.edge
        · subst e
          exact False.elim (ExpansionPaths.copy_no_internal C H copy v)
        · exact .inr ⟨⟨e,eq⟩,v⟩
  invFun x := match x with
    | .inl v => ⟨.inl v.val,fun eq => v.property (Sum.inl.inj eq)⟩
    | .inr ⟨e,v⟩ => ⟨.inr ⟨e.val,v⟩,by simp⟩
  left_inv := by
    rintro ⟨v,ne⟩
    cases v with
    | inl v => rfl
    | inr pair =>
        obtain ⟨e,v⟩ := pair
        by_cases eq : e = f.edge
        · subst e; exact False.elim (ExpansionPaths.copy_no_internal C H copy v)
        · simp only [dite_eq_right eq]
  right_inv := by
    intro x
    cases x with
    | inl v => rfl
    | inr pair =>
        obtain ⟨e,v⟩ := pair
        simp only [dite_eq_right e.property]

/-- Deleting the copied focus edge deletes exactly its owning singleton fibre. -/
def edges : Bijection (erasedExpansion C H f copy free t ht).Edge
    ((erased C f t ht).expand (family C H f t ht)).Edge where
  toFun x := ⟨⟨x.val.1,by
    intro eq
    obtain ⟨⟨e,v⟩,ne⟩ := x
    dsimp at eq
    subst e
    exact ne (congrArg (Sigma.mk f.edge) (copy.only v))⟩,x.val.2⟩
  invFun x := ⟨⟨x.1.val,x.2⟩,fun eq => x.1.property (congrArg Sigma.fst eq)⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem keep_host (v : C.Vertex) (ne : v ≠ .internal t) :
    Port.map (vertices C H f copy free t ht).toFun
      (FocusErasure.keep (G := C.expand H) (.inl t) (Net.Expansion.host C H v)
        (fun eq => ne (Net.Expansion.host_injective C H eq))) =
    Net.Expansion.host (erased C f t ht) (family C H f t ht) (FocusErasure.keep t v ne) := by
  cases v <;> rfl

theorem contract_host (v : C.Vertex) :
    Port.map (vertices C H f copy free t ht).toFun
      (FocusErasure.contract (focus C H f copy free) (.inl t)
        (congrArg (Net.Expansion.host C H) ht) (Net.Expansion.host C H v)) =
    Net.Expansion.host (erased C f t ht) (family C H f t ht)
      (FocusErasure.contract f t ht v) := by
  classical
  by_cases eq : v = .internal t
  · subst v
    change Port.map _ (FocusErasure.contract (focus C H f copy free) (.inl t)
      (congrArg (Net.Expansion.host C H) ht) (.internal (.inl t))) = _
    rw [FocusErasure.contract_target (focus C H f copy free) (.inl t)
      (congrArg (Net.Expansion.host C H) ht), FocusErasure.contract_target f t ht]
    change Port.map _ (FocusErasure.keep (G := C.expand H) _ (Net.Expansion.host C H f.source) _) = _
    exact keep_host C H f copy free t ht f.source (FocusErasure.source_ne_target f t ht)
  · have ne : Net.Expansion.host C H v ≠ .internal (.inl t) :=
      fun h => eq (Net.Expansion.host_injective C H h)
    simp only [FocusErasure.contract, dite_eq_right eq, dite_eq_right ne]
    exact keep_host C H f copy free t ht v eq

theorem sourcePort (e : (erased C f t ht).Edge)
    (i : Fin ((alphabet ops d).signature.input (C.edgeLabel e.val)).length) :
    (erased C f t ht).sourcePort e i = FocusErasure.contract f t ht (C.sourcePort e.val i) := by
  simp [Net.sourcePort, erased, FocusErasure.erase]

theorem targetPort (e : (erased C f t ht).Edge)
    (i : Fin ((alphabet ops d).signature.output (C.edgeLabel e.val)).length) :
    (erased C f t ht).targetPort e i = FocusErasure.contract f t ht (C.targetPort e.val i) := by
  simp [Net.targetPort, erased, FocusErasure.erase]

/-- Joining the focus endpoints commutes with every insertion at a retained edge. -/
theorem contract_insert (e : (erased C f t ht).Edge) (v : (H e.val).Vertex) :
    Port.map (vertices C H f copy free t ht).toFun
      (FocusErasure.contract (focus C H f copy free) (.inl t)
        (congrArg (Net.Expansion.host C H) ht) (Net.Expansion.insert C H e.val v)) =
    Net.Expansion.insert (erased C f t ht) (family C H f t ht) e v := by
  cases v with
  | internal v => simp [Net.Expansion.insert,FocusErasure.contract,FocusErasure.keep,
      Port.map,vertices,e.property]
  | input i =>
      change Port.map _ (FocusErasure.contract (focus C H f copy free) (.inl t) (congrArg (Net.Expansion.host C H) ht) (Net.Expansion.host C H (C.sourcePort e.val i))) =
        Net.Expansion.host _ _ ((erased C f t ht).sourcePort e i)
      rw [contract_host,sourcePort]
  | output i =>
      change Port.map _ (FocusErasure.contract (focus C H f copy free) (.inl t) (congrArg (Net.Expansion.host C H) ht) (Net.Expansion.host C H (C.targetPort e.val i))) =
        Net.Expansion.host _ _ ((erased C f t ht).targetPort e i)
      rw [contract_host,targetPort]

/-- Erasing after expansion is isomorphic to expanding the erased context. -/
noncomputable def iso : Net.Iso (erasedExpansion C H f copy free t ht)
    ((erased C f t ht).expand (family C H f t ht)) where
  vertices := vertices C H f copy free t ht
  edges := edges C H f copy free t ht
  internal_label := by
    rintro ⟨v,ne⟩
    cases v with
    | inl v => rfl
    | inr pair =>
        obtain ⟨e,v⟩ := pair
        by_cases eq : e = f.edge
        · subst e; exact False.elim (ExpansionPaths.copy_no_internal C H copy v)
        · simp [vertices,eq,Net.Expansion.internalLabel,family]
  edge_label _ := rfl
  source := by
    intro e
    change ((((H e.val.1).source e.val.2).map (Net.Expansion.insert C H e.val.1)).map
      (FocusErasure.contract (focus C H f copy free) (.inl t) (congrArg (Net.Expansion.host C H) ht))).map
      (Port.map (vertices C H f copy free t ht).toFun) =
      ((H e.val.1).source e.val.2).map (Net.Expansion.insert (erased C f t ht)
        (family C H f t ht) ((edges C H f copy free t ht).toFun e).1)
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    exact contract_insert C H f copy free t ht ((edges C H f copy free t ht).toFun e).1 v
  target := by
    intro e
    change ((((H e.val.1).target e.val.2).map (Net.Expansion.insert C H e.val.1)).map
      (FocusErasure.contract (focus C H f copy free) (.inl t) (congrArg (Net.Expansion.host C H) ht))).map
      (Port.map (vertices C H f copy free t ht).toFun) =
      ((H e.val.1).target e.val.2).map (Net.Expansion.insert (erased C f t ht)
        (family C H f t ht) ((edges C H f copy free t ht).toFun e).1)
    simp only [List.map_map]
    apply List.map_congr_left
    intro v _
    exact contract_insert C H f copy free t ht ((edges C H f copy free t ht).toFun e).1 v

/-- The commutation isomorphism also identifies the distinguished join coordinate. -/
theorem position :
    Port.map (iso C H f copy free t ht).vertices.toFun
      (FocusErasure.position (focus C H f copy free) (.inl t)
        (congrArg (Net.Expansion.host C H) ht)) =
    Net.Expansion.host (erased C f t ht) (family C H f t ht) (FocusErasure.position f t ht) :=
  keep_host C H f copy free t ht f.source (FocusErasure.source_ne_target f t ht)

/-- The canonical underlying graph uses a chosen target; uniqueness of the
focus target transfers the commutation theorem to that choice. -/
theorem underlying_exists :
    ∃ a : Net.Iso (focus C H f copy free).underlying
      (f.underlying.expand (family C H f f.targetVertex f.targetVertex_spec)),
    Port.map a.vertices.toFun
      (FocusErasure.position (focus C H f copy free) (focus C H f copy free).targetVertex
        (focus C H f copy free).targetVertex_spec) =
      Net.Expansion.host f.underlying (family C H f f.targetVertex f.targetVertex_spec)
        (FocusErasure.position f f.targetVertex f.targetVertex_spec) := by
  have aux : ∀ u (hu : (focus C H f copy free).target = .internal u),
      ∃ a : Net.Iso (FocusErasure.erase (focus C H f copy free) u hu)
        (f.underlying.expand (family C H f f.targetVertex f.targetVertex_spec)),
      Port.map a.vertices.toFun (FocusErasure.position (focus C H f copy free) u hu) =
        Net.Expansion.host f.underlying (family C H f f.targetVertex f.targetVertex_spec)
          (FocusErasure.position f f.targetVertex f.targetVertex_spec) := by
    intro u hu
    have target : (focus C H f copy free).target = .internal (.inl f.targetVertex) :=
      congrArg (Net.Expansion.host C H) f.targetVertex_spec
    have eq : u = .inl f.targetVertex := Port.internal.inj (hu.symm.trans target)
    subst u
    exact ⟨iso C H f copy free f.targetVertex f.targetVertex_spec,
      position C H f copy free f.targetVertex f.targetVertex_spec⟩
  exact aux _ _

end Hypernets.Linear.ExpansionErasure

namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat}

/-- The coordinate of a focussed context, which may still contain holes. -/
noncomputable def Focussed.coordinate {C : Hypernet ops d [.term] []} (f : Focussed C) :
    TypedPosition f.underlying :=
  ⟨(f.mode,FocusErasure.position f f.targetVertex f.targetVertex_spec),
    FocusErasure.position_term f f.targetVertex f.targetVertex_spec⟩

namespace ExpansionErasure
variable (C : Hypernet ops d [.term] [])
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (f : Focussed C) (copy : ExpansionPaths.CorollaCopy C H f.edge)
    (free : ∀ e, e ≠ f.edge → FocusFree (H e))

/-- Restrict the family to the non-focus edges of the canonical erased context. -/
noncomputable abbrev erasedFamily := family C H f f.targetVertex f.targetVertex_spec

include copy free in
theorem expanded_free : FocusFree (f.underlying.expand (erasedFamily C H f)) := by
  obtain ⟨a,_⟩ := underlying_exists C H f copy free
  exact (DeepIso.focusFree_iff (DeepIso.ofIso a)).mp (focus C H f copy free).underlying_focusFree

include copy free in
theorem expanded_closed (closed : HoleFree (C.expand H)) :
    HoleFree (f.underlying.expand (erasedFamily C H f)) := by
  obtain ⟨a,_⟩ := underlying_exists C H f copy free
  exact (DeepIso.holeFree_iff (DeepIso.ofIso a)).mp
    ((focus C H f copy free).underlying_holeFree closed)

/-- Filling then inserting at the transported coordinate reconstructs expansion
of the original focussed context, including its distinguished focus and mode. -/
noncomputable def realization_iso (closed : HoleFree (C.expand H)) :
    Focussed.Iso
      (((f.coordinate).expand (erasedFamily C H f)).realize
        (expanded_free C H f copy free) (expanded_closed C H f copy free closed)).focussed
      (ExpansionPaths.state H f copy free closed).focussed := by
  let a := Classical.choose (underlying_exists C H f copy free)
  have pos := Classical.choose_spec (underlying_exists C H f copy free)
  let s := ExpansionPaths.state H f copy free closed
  have eq : (State.coordinate s).rename a = f.coordinate.expand (erasedFamily C H f) := by
    apply Subtype.ext
    exact Prod.ext rfl pos
  have transported := (State.coordinate s).realize_rename a s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free) (expanded_free C H f copy free)
    (expanded_closed C H f copy free closed)
  rw [eq] at transported
  exact transported.symm.trans (State.recover s)

end ExpansionErasure
end Hypernets.Linear

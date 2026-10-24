import Hypernets.Graph.SearchRealization

/-! Erasure of a focus with internal target: delete the focus edge and identify
its target with its source. Every closed focussed state has an internal target. -/
namespace Hypernets.Linear.FocusErasure
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {I : List Wire}
    {G : Hypernet ops d I []} (f : Focussed G) (t : G.Internal)
    (target_eq : f.target = .internal t)

abbrev Vertex := Port {x : G.Internal // x ≠ t} I.length 0

def lift : Vertex (G := G) t → G.Vertex := Port.map Subtype.val

def keep (w : G.Vertex) (ne : w ≠ .internal t) : Vertex (G := G) t :=
  match w with
  | .internal x => .internal ⟨x, fun eq => ne (congrArg Port.internal eq)⟩
  | .input i => .input i
  | .output i => .output i

theorem lift_keep (w : G.Vertex) (ne : w ≠ .internal t) : lift t (keep t w ne) = w := by
  cases w <;> rfl

theorem lift_injective {a b : Vertex (G := G) t} (eq : lift t a = lift t b) : a = b :=
  Port.map_injective (fun _ _ h => Subtype.ext h) eq

theorem lift_ne_target (x : Vertex (G := G) t) : lift t x ≠ .internal t := by
  cases x with
  | internal x => exact fun eq => x.property (Port.internal.inj eq)
  | input _ => intro eq; cases eq
  | output _ => intro eq; cases eq

include target_eq in
theorem source_ne_target : f.source ≠ .internal t := by
  simpa only [← target_eq] using f.self_acyclic

/-- The erased graph's distinguished vertex represents both focus endpoints. -/
def position : Vertex (G := G) t := keep t f.source (source_ne_target f t target_eq)

noncomputable def contract (w : G.Vertex) : Vertex (G := G) t := by
  classical
  exact if h : w = .internal t then position f t target_eq else keep t w h

theorem lift_position : lift t (position f t target_eq) = f.source :=
  lift_keep t _ _

theorem contract_target : contract f t target_eq (.internal t) = position f t target_eq := by
  simp [contract]

theorem lift_contract (w : G.Vertex) (ne : w ≠ .internal t) :
    lift t (contract f t target_eq w) = w := by
  simp [contract, ne, lift_keep]

theorem contract_lift (x : Vertex (G := G) t) : contract f t target_eq (lift t x) = x := by
  apply lift_injective t
  exact lift_contract f t target_eq _ (lift_ne_target t x)

theorem contract_source : contract f t target_eq f.source = position f t target_eq := by
  simp [contract, source_ne_target f t target_eq, position]

/-- Recover the pre-erasure source vertex, choosing the old target at the join. -/
noncomputable def expand (x : Vertex (G := G) t) : G.Vertex := by
  classical
  exact if lift t x = f.source then .internal t else lift t x

include target_eq in
theorem expand_ne_source (x : Vertex (G := G) t) : expand f t x ≠ f.source := by
  classical
  by_cases eq : lift t x = f.source
  · simpa [expand, eq] using (source_ne_target f t target_eq).symm
  · simp [expand, eq]

theorem expand_contract (w : G.Vertex) (ne : w ≠ f.source) :
    expand f t (contract f t target_eq w) = w := by
  classical
  by_cases eq : w = .internal t
  · subst w; simp [contract_target, expand, lift_position]
  · simp [expand, lift_contract f t target_eq w eq, ne]

theorem contract_expand (x : Vertex (G := G) t) : contract f t target_eq (expand f t x) = x := by
  classical
  by_cases eq : lift t x = f.source
  · simp only [expand, ite_eq_left eq, contract_target]
    apply lift_injective t
    exact (lift_position f t target_eq).trans eq.symm
  · simp only [expand, ite_eq_right eq, contract_lift]

theorem source_avoids {e : G.Edge} (ne : e ≠ f.edge) {w : G.Vertex} (mem : w ∈ G.source e) : w ≠ f.source := by
  intro eq
  subst w
  exact ne (G.source_unique mem (by rw [f.source_eq]; simp))

include target_eq in
theorem target_avoids {e : G.Edge} (ne : e ≠ f.edge) {w : G.Vertex} (mem : w ∈ G.target e) : w ≠ .internal t := by
  intro eq
  subst w
  exact ne (G.target_unique mem (by rw [f.target_eq, target_eq]; simp))

theorem source_injective {a b : G.Vertex} (ha : a ≠ f.source) (hb : b ≠ f.source)
    (eq : contract f t target_eq a = contract f t target_eq b) : a = b := by
  have h := congrArg (expand f t) eq
  simpa only [expand_contract f t target_eq a ha, expand_contract f t target_eq b hb] using h

theorem target_injective {a b : G.Vertex} (ha : a ≠ .internal t) (hb : b ≠ .internal t)
    (eq : contract f t target_eq a = contract f t target_eq b) : a = b := by
  have h := congrArg (lift t) eq
  simpa only [lift_contract f t target_eq a ha, lift_contract f t target_eq b hb] using h

theorem source_term : G.vertexLabel f.source = .term := by
  have h := G.source_typed f.edge
  rw [f.source_eq, f.label] at h
  cases d <;> simpa [focusLabel, alphabet, baseAlphabet, nextAlphabet, primitiveSignature, Net.vertexLabel] using h

include target_eq in
theorem target_term : G.internalLabel t = .term := by
  have h := G.target_typed f.edge
  rw [f.target_eq, target_eq, f.label] at h
  cases d <;> simpa [focusLabel, alphabet, baseAlphabet, nextAlphabet, primitiveSignature, Port.label] using h

theorem keep_label (w : G.Vertex) (ne : w ≠ .internal t) :
    Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (keep t w ne) = G.vertexLabel w := by
  cases w <;> rfl

theorem contract_label (w : G.Vertex) :
    Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (contract f t target_eq w) = G.vertexLabel w := by
  classical
  by_cases eq : w = .internal t
  · subst w
    rw [contract_target]
    change Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (keep t f.source (source_ne_target f t target_eq)) = G.internalLabel t
    rw [keep_label, source_term f, target_term f t target_eq]
  · simp [contract, eq, keep_label]

/-- Delete the focus edge and the internal target, contracting all incidences. -/
@[reducible] noncomputable def erase : Hypernet ops d I [] where
  Internal := {x : G.Internal // x ≠ t}
  Edge := {e : G.Edge // e ≠ f.edge}
  finiteInternal := G.finiteInternal.subtype _
  finiteEdge := G.finiteEdge.subtype _
  internalLabel x := G.internalLabel x.val
  edgeLabel e := G.edgeLabel e.val
  source e := (G.source e.val).map (contract f t target_eq)
  target e := (G.target e.val).map (contract f t target_eq)
  source_nodup e := nodup_map_on (G.source_nodup e.val) (fun _ ha _ hb eq =>
    source_injective f t target_eq (source_avoids f e.property ha) (source_avoids f e.property hb) eq)
  target_nodup e := nodup_map_on (G.target_nodup e.val) (fun _ ha _ hb eq =>
    target_injective f t target_eq (target_avoids f t target_eq e.property ha) (target_avoids f t target_eq e.property hb) eq)
  source_unique := by
    intro x e k he hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hk
    have same := source_injective f t target_eq (source_avoids f k.property hb) (source_avoids f e.property ha) eq
    subst b
    exact Subtype.ext (G.source_unique ha hb)
  target_unique := by
    intro x e k he hk
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
    obtain ⟨b, hb, eq⟩ := List.mem_map.mp hk
    have same := target_injective f t target_eq (target_avoids f t target_eq k.property hb) (target_avoids f t target_eq e.property ha) eq
    subst b
    exact Subtype.ext (G.target_unique ha hb)
  source_coverage := by
    intro x
    constructor
    · intro _; cases x with
      | internal _ => exact id
      | input _ => exact id
      | output i => exact Fin.elim0 i
    · intro _
      have no : ¬ (expand f t x).IsOutput := by
        cases expand f t x with
        | internal _ => exact id
        | input _ => exact id
        | output i => exact Fin.elim0 i
      obtain ⟨e, he⟩ := (G.source_coverage _).mpr no
      have ne : e ≠ f.edge := by
        intro eq
        rw [eq, f.source_eq] at he
        exact expand_ne_source f t target_eq x (List.mem_singleton.mp he)
      exact ⟨⟨e, ne⟩, List.mem_map.mpr ⟨_, he, contract_expand f t target_eq x⟩⟩
  target_coverage := by
    intro x
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨w, hw, eq⟩ := List.mem_map.mp he
      have same := congrArg (lift t) eq
      rw [lift_contract f t target_eq w (target_avoids f t target_eq e.property hw)] at same
      have no := G.target_not_input hw
      rw [same] at no
      simpa [lift] using no
    · intro hx
      have no : ¬ (lift t x).IsInput := by simpa [lift] using hx
      obtain ⟨e, he⟩ := (G.target_coverage _).mpr no
      have ne : e ≠ f.edge := by
        intro eq
        rw [eq, f.target_eq, target_eq] at he
        exact lift_ne_target t x (List.mem_singleton.mp he)
      exact ⟨⟨e, ne⟩, List.mem_map.mpr ⟨_, he, contract_lift f t target_eq x⟩⟩
  source_typed e := by
    rw [List.map_map]
    have eq : (fun w => Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (contract f t target_eq w)) = G.vertexLabel := funext (contract_label f t target_eq)
    change (G.source e.val).map (fun w => Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (contract f t target_eq w)) = _
    rw [eq]
    exact G.source_typed e.val
  target_typed e := by
    rw [List.map_map]
    have eq : (fun w => Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (contract f t target_eq w)) = G.vertexLabel := funext (contract_label f t target_eq)
    change (G.target e.val).map (fun w => Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (contract f t target_eq w)) = _
    rw [eq]
    exact G.target_typed e.val

theorem erased_focusFree : FocusFree (erase f t target_eq) :=
  fun e => f.other_free e.val e.property

theorem position_term : (erase f t target_eq).vertexLabel (position f t target_eq) = .term := by
  change Port.label (I := I) (O := []) (fun x : {x : G.Internal // x ≠ t} => G.internalLabel x.val) (keep t f.source (source_ne_target f t target_eq)) = .term
  rw [keep_label, source_term f]

theorem erased_holeFree (free : HoleFree G) : HoleFree (erase f t target_eq) := by
  intro h present
  obtain ⟨⟨e, p⟩, hp⟩ := (hasHole_iff_occurrences _ h).mp present
  exact free h ((hasHole_iff_occurrences G h).mpr ⟨⟨e.val, p⟩, hp⟩)

end Hypernets.Linear.FocusErasure

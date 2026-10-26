import Hypernets.Copying.EqualityCoherenceExamples

/-! Typed target-only rewiring: source incidences and all existing carriers are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.TargetSwap
open Graph

/-- Exchange two values, including the degenerate case where they are equal. -/
noncomputable def exchange {A : Type} (a b x : A) : A := by
  classical
  exact if x = a then b else if x = b then a else x

theorem exchange_left {A : Type} (a b : A) : exchange a b a = b := by simp [exchange]
theorem exchange_right {A : Type} (a b : A) : exchange a b b = a := by
  classical
  by_cases eq : a = b
  · subst b; simp [exchange]
  · simp [exchange,Ne.symm eq]
theorem exchange_other {A : Type} {a b x : A} (ha : x ≠ a) (hb : x ≠ b) : exchange a b x = x := by
  simp [exchange,ha,hb]

theorem exchange_involutive {A : Type} (a b x : A) : exchange a b (exchange a b x) = x := by
  classical
  by_cases ha : x = a
  · subst x; rw [exchange_left,exchange_right]
  · by_cases hb : x = b
    · subst x; rw [exchange_right,exchange_left]
    · rw [exchange_other ha hb,exchange_other ha hb]

noncomputable def permutation {A : Type} (a b : A) : Bijection A A :=
  ⟨exchange a b,exchange a b,exchange_involutive a b,exchange_involutive a b⟩

/-- Commutation needs injectivity only at the three ports being compared. -/
theorem exchange_map {A B : Type} (f : A → B) (a b x : A)
    (ha : f x = f a → x = a) (hb : f x = f b → x = b) :
    exchange (f a) (f b) (f x) = f (exchange a b x) := by
  classical
  by_cases xa : x = a
  · subst x; rw [exchange_left,exchange_left]
  · by_cases xb : x = b
    · subst x; rw [exchange_right,exchange_right]
    · rw [exchange_other (fun h => xa (ha h)) (fun h => xb (hb h)),exchange_other xa xb]

/-- Permute target endpoints while retaining source incidences, labels and carrier types. -/
@[reducible] def reindex {d I O} (G : Hypernet d I O) (p : Bijection G.Vertex G.Vertex)
    (input : ∀ v, (p.toFun v).IsInput ↔ v.IsInput)
    (typed : ∀ v, G.vertexLabel (p.toFun v) = G.vertexLabel v) : Hypernet d I O where
  Internal := G.Internal
  Edge := G.Edge
  finiteInternal := G.finiteInternal
  finiteEdge := G.finiteEdge
  internalLabel := G.internalLabel
  edgeLabel := G.edgeLabel
  source := G.source
  target e := (G.target e).map p.toFun
  source_nodup := G.source_nodup
  target_nodup e := nodup_map_on (G.target_nodup e) (fun _ _ _ _ h => p.injective h)
  source_unique := G.source_unique
  target_unique := by
    intro v e f he hf
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
    obtain ⟨b,hb,eq⟩ := List.mem_map.mp hf
    have eq := p.injective eq; subst b
    exact G.target_unique ha hb
  source_coverage := G.source_coverage
  target_coverage v := by
    constructor
    · rintro ⟨e,he⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
      exact fun h => G.target_not_input ha ((input a).mp h)
    · intro hv
      have no : ¬ (p.invFun v).IsInput := fun h => hv (by simpa only [p.right_inv] using (input _).mpr h)
      obtain ⟨e,he⟩ := (G.target_coverage _).mpr no
      exact ⟨e,List.mem_map.mpr ⟨_,he,p.right_inv v⟩⟩
  source_typed := G.source_typed
  target_typed e := by
    change ((G.target e).map p.toFun).map G.vertexLabel = _
    rw [List.map_map]
    exact (List.map_congr_left (fun v _ => typed v)).trans (G.target_typed e)

/-- Identity target permutation changes no graph field. -/
theorem reindex_refl {d I O} (G : Hypernet d I O) :
    reindex G (Bijection.refl _) (fun _ => Iff.rfl) (fun _ => rfl) = G := by
  cases G
  simp only [reindex,Bijection.refl,List.map_id_fun]
  rfl

/-- Exchanging two non-input ports preserves boundary classification. -/
theorem input_iff {d I O} {G : Hypernet d I O} {a b : G.Vertex}
    (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (x : G.Vertex) :
    (exchange a b x).IsInput ↔ x.IsInput := by
  classical
  by_cases ha : x = a
  · subst x; rw [exchange_left]; simp only [na,nb]
  · by_cases hb : x = b
    · subst x; rw [exchange_right]; simp only [na,nb]
    · rw [exchange_other ha hb]

/-- Exchanging equally typed ports preserves every target's wire type. -/
theorem typed {d I O} {G : Hypernet d I O} {a b : G.Vertex}
    (eq : G.vertexLabel a = G.vertexLabel b) (x : G.Vertex) :
    G.vertexLabel (exchange a b x) = G.vertexLabel x := by
  classical
  by_cases ha : x = a
  · subst x; rw [exchange_left]; exact eq.symm
  · by_cases hb : x = b
    · subst x; rw [exchange_right]; exact eq
    · rw [exchange_other ha hb]

/-- Swap two equally typed target endpoints without changing either source incidence. -/
@[reducible] noncomputable def net {d I O} (G : Hypernet d I O) (a b : G.Vertex)
    (na : ¬ a.IsInput) (nb : ¬ b.IsInput) (eq : G.vertexLabel a = G.vertexLabel b) : Hypernet d I O :=
  reindex G (permutation a b) (input_iff na nb) (typed eq)
end Hypernets.Copying.TargetSwap

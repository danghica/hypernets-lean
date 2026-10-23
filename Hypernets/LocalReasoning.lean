import Hypernets.Contextual

/-!
An abstract specimen interface for the forward clause of Theorem 6.

IMPORTANT: this proves the logical argument *conditional on* graph locality
laws. It does not yet instantiate the interface with the paper's hypernets.
In particular `SpecimenSystem.context_step` is the graph obligation corresponding
to Lemma 39(3), and `initial_lift` in `contextual_sufficiency` is Proposition 38's
initial-specimen obligation. They must be proved, not postulated globally.
-/

namespace Hypernets

inductive Focus where
  | search | backtrack | rewrite
  deriving DecidableEq

universe u v

/-- The facts about specimens used by the forward proof of Proposition 40.
`Specimen` will eventually package a focussed multi-hole context and two
type-correct, pointwise related vectors of focus-free hypernets. -/
structure SpecimenSystem {State : Type u} (M : Machine State) where
  Specimen : Type v
  left : Specimen → State
  right : Specimen → State
  mode : Specimen → Focus
  entering : Specimen → Prop
  rooted : State → Prop
  rooted_step : ∀ {s t}, rooted s → M.step s t → rooted t
  same_final : ∀ c, M.final (left c) ↔ M.final (right c)
  /-- Context-only traversal, supplied by graph locality and output-closure. -/
  context_step : ∀ c, rooted (left c) → rooted (right c) →
    (mode c = .backtrack ∨ (mode c = .search ∧ ¬ entering c)) →
    ((∃ s', M.step (left c) s') ∨ (∃ t', M.step (right c) t')) →
      ∃ d, (mode d ≠ .rewrite ∨ ¬ entering d) ∧
        M.step (left c) (left d) ∧ M.step (right c) (right d)

namespace SpecimenSystem

variable {State : Type u} {M : Machine State} (G : SpecimenSystem.{u,v} M)

/-- Remote excludes only an entering rewrite focus (Appendix F). -/
def Remote (c : G.Specimen) : Prop := G.mode c ≠ .rewrite ∨ ¬ G.entering c

def Settled (c : G.Specimen) : Prop :=
  G.mode c = .backtrack ∨ (G.mode c = .search ∧ ¬ G.entering c)

def Lifting (s t : State) : Prop :=
  ∃ c, G.Remote c ∧ G.rooted (G.left c) ∧ G.rooted (G.right c) ∧
    s = G.left c ∧ t = G.right c

theorem settled_remote {c : G.Specimen} (h : G.Settled c) : G.Remote c := by
  left
  rcases h with hb | ⟨hs, _⟩ <;> simp_all

theorem rooted_steps {n s t} (hs : G.rooted s) (h : M.Steps n s t) :
    G.rooted t := by
  induction h with
  | zero => exact hs
  | cons st _ ih => exact ih (G.rooted_step hs st)

/-- A non-rewrite quasi-specimen after rootedness and mode compatibility have
been discharged. Unlike `Lifting`, its endpoints may be related up to refinement.
This is the consequence of §8.1(2) consumed by the proof. -/
def Quasi (A B : State → State → Prop) (s t : State) : Prop :=
  G.rooted s → G.rooted t →
    ∃ c, G.mode c ≠ .rewrite ∧ G.rooted (G.left c) ∧ G.rooted (G.right c) ∧
      A s (G.left c) ∧ B (G.right c) t

theorem quasi_upTo {P S : CostOrder} {s t : State}
    (h : G.Quasi (M.Refines P) (M.Refines S) s t)
    (hs : G.rooted s) (ht : G.rooted t) : M.UpTo P S G.Lifting s t := by
  obtain ⟨c, mode, hl, hr, before, after⟩ := h hs ht
  exact ⟨G.left c, G.right c, before,
    ⟨c, Or.inl mode, hl, hr, rfl, rfl⟩, after⟩

/-- §8.2, after restricting to the rooted specimens used by contextual lifting.
Case III keeps equivalence, rather than silently replacing it by refinement. -/
def InputSafe (Q P : CostOrder) : Prop :=
  ∀ c, G.rooted (G.left c) → G.rooted (G.right c) →
    G.mode c = .search → G.entering c →
    (∃ k l s t, M.Steps k (G.left c) s ∧ M.Stuck s ∧
      M.Steps l (G.right c) t ∧ M.Stuck t) ∨
    (∃ d k l, G.Settled d ∧ Q.rel (1 + k) l ∧
      M.Steps (1 + k) (G.left c) (G.left d) ∧
      M.Steps l (G.right c) (G.right d)) ∨
    (∃ k l s t, Q.rel (1 + k) (1 + l) ∧
      M.Steps (1 + k) (G.left c) s ∧ M.Steps (1 + l) (G.right c) t ∧
      G.Quasi (M.Equiv P) (M.Equiv P) s t)

/-- §8.3, restricted to rooted remote specimens. This removes precisely the
unrooted disjunct, which is contradictory for members of contextual lifting. -/
def Robust (Q P S : CostOrder) : Prop :=
  ∀ c, G.rooted (G.left c) → G.rooted (G.right c) →
    G.mode c = .rewrite → ¬ G.entering c →
    ∀ {s'}, M.step (G.left c) s' →
      (∃ k z, M.Steps k s' z ∧ M.Stuck z) ∨
      ∃ k l s t, Q.rel (1 + k) l ∧ M.Steps k s' s ∧
        M.Steps l (G.right c) t ∧ G.Quasi (M.Refines P) (M.Refines S) s t

/-- Abstract forward Proposition 40, conditional on the locality interface. -/
theorem countingSimulation {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q P)
    (robust : G.Robust Q P S) : M.CountingSimulation Q P S G.Lifting where
  final_match := by
    rintro s t ⟨c, _, _, _, rfl, rfl⟩ hs
    exact (G.same_final c).mp hs
  progress := by
    rintro s t s' ⟨c, remote, hl, hr, rfl, rfl⟩ step
    have context_case (settled : G.Settled c) :=
      G.context_step c hl hr settled (Or.inl ⟨s', step⟩)
    have settled_case (settled : G.Settled c) :
        (∃ k z, M.Steps k s' z ∧ M.Stuck z) ∨
        ∃ k l h₁ h₂, M.Steps k s' h₁ ∧ M.Steps l (G.right c) h₂ ∧
          Q.rel (1 + k) l ∧ M.UpTo P S G.Lifting h₁ h₂ := by
      obtain ⟨d, rd, leftStep, rightStep⟩ := context_case settled
      have eq := det step leftStep
      right
      refine ⟨0, 1, G.left d, G.right d, eq ▸ .zero s',
        .cons rightStep (.zero _), Q.refl 1, ?_⟩
      exact ⟨_, _, Machine.Refines.refl P _,
        ⟨d, rd, G.rooted_step hl leftStep, G.rooted_step hr rightStep, rfl, rfl⟩,
        Machine.Refines.refl S _⟩
    cases mode : G.mode c with
    | backtrack => exact settled_case (Or.inl mode)
    | search =>
        by_cases entering : G.entering c
        · rcases safe c hl hr mode entering with stuck | direct | quasi
          · obtain ⟨k, l, a, b, runa, ha, _, _⟩ := stuck
            obtain ⟨j, tail⟩ := runa.stuck_after_step det step ha
            exact Or.inl ⟨j, a, tail, ha⟩
          · obtain ⟨d, k, l, settled, cost, runa, runb⟩ := direct
            have tail := (show M.Steps (k + 1) (G.left c) (G.left d) by
              simpa [Nat.add_comm] using runa).drop_first det step
            right
            refine ⟨k, l, _, _, tail, runb, cost, ?_⟩
            exact ⟨_, _, Machine.Refines.refl P _,
              ⟨d, G.settled_remote settled, G.rooted_steps hl runa,
                G.rooted_steps hr runb, rfl, rfl⟩, Machine.Refines.refl S _⟩
          · obtain ⟨k, l, a, b, cost, runa, runb, quasi⟩ := quasi
            have tail := (show M.Steps (k + 1) (G.left c) a by
              simpa [Nat.add_comm] using runa).drop_first det step
            have qa : G.Quasi (M.Refines P) (M.Refines S) a b := by
              intro ha hb
              obtain ⟨d, md, hdl, hdr, before, after⟩ := quasi ha hb
              exact ⟨d, md, hdl, hdr, before.1,
                after.1.mono reasonable.left_in_right⟩
            exact Or.inr ⟨k, 1 + l, a, b, tail, runb, cost,
              G.quasi_upTo qa (G.rooted_steps hl runa) (G.rooted_steps hr runb)⟩
        · exact settled_case (Or.inr ⟨mode, entering⟩)
    | rewrite =>
        have notEntering : ¬ G.entering c := by
          rcases remote with notRewrite | notEntering
          · exact False.elim (notRewrite mode)
          · exact notEntering
        rcases robust c hl hr mode notEntering step with stuck | matching
        · exact Or.inl stuck
        · obtain ⟨k, l, a, b, cost, runa, runb, quasi⟩ := matching
          exact Or.inr ⟨k, l, a, b, runa, runb, cost,
            G.quasi_upTo quasi (G.rooted_steps (G.rooted_step hl step) runa)
              (G.rooted_steps hr runb)⟩

/-- Abstract forward sufficiency theorem; the concrete hypernet instance remains
an explicit obligation, rather than an axiom hidden in this theorem. -/
theorem sufficiency {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q P)
    (robust : G.Robust Q P S) {s t} (related : G.Lifting s t) :
    M.Refines Q s t :=
  (G.countingSimulation det reasonable safe robust).sound det reasonable related

/-- Swapping the two vectors of a specimen (Appendix F.9). -/
def opposite : SpecimenSystem M where
  Specimen := G.Specimen
  left := G.right
  right := G.left
  mode := G.mode
  entering := G.entering
  rooted := G.rooted
  rooted_step := G.rooted_step
  same_final c := (G.same_final c).symm
  context_step := by
    intro c hr hl settled available
    obtain ⟨d, remote, left, right⟩ :=
      G.context_step c hl hr settled available.symm
    exact ⟨d, remote, right, left⟩

theorem lifting_opposite {s t : State} : G.opposite.Lifting s t ↔ G.Lifting t s := by
  constructor
  · rintro ⟨c, remote, hr, hl, rfl, rfl⟩
    exact ⟨c, remote, hl, hr, rfl, rfl⟩
  · rintro ⟨c, remote, hl, hr, rfl, rfl⟩
    exact ⟨c, remote, hr, hl, rfl, rfl⟩

/-- Abstract reverse Proposition 40. The safety hypothesis is on the original
template with the converse cost relation; robustness is on its converse.
The zero-step subcase of safety II needs an additional context traversal. -/
theorem countingSimulation_converse {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q.converse P)
    (robust : G.opposite.Robust Q P S) :
    M.CountingSimulation Q P S G.opposite.Lifting where
  final_match := by
    rintro s t ⟨c, _, _, _, rfl, rfl⟩ hs
    exact (G.same_final c).mpr hs
  progress := by
    rintro s t s' ⟨c, remote, hr, hl, rfl, rfl⟩ step
    have settled_case (settled : G.Settled c) :
        (∃ k z, M.Steps k s' z ∧ M.Stuck z) ∨
        ∃ k l h₁ h₂, M.Steps k s' h₁ ∧ M.Steps l (G.left c) h₂ ∧
          Q.rel (1 + k) l ∧ M.UpTo P S G.opposite.Lifting h₁ h₂ := by
      obtain ⟨d, rd, leftStep, rightStep⟩ :=
        G.context_step c hl hr settled (Or.inr ⟨s', step⟩)
      have eq := det step rightStep
      right
      refine ⟨0, 1, G.right d, G.left d, eq ▸ .zero s',
        .cons leftStep (.zero _), Q.refl 1, ?_⟩
      exact ⟨_, _, Machine.Refines.refl P _,
        ⟨d, rd, G.rooted_step hr rightStep, G.rooted_step hl leftStep, rfl, rfl⟩,
        Machine.Refines.refl S _⟩
    cases mode : G.mode c with
    | backtrack => exact settled_case (Or.inl mode)
    | search =>
        by_cases entering : G.entering c
        · rcases safe c hl hr mode entering with stuck | direct | quasi
          · obtain ⟨_, _, _, b, _, _, runb, hb⟩ := stuck
            obtain ⟨j, tail⟩ := runb.stuck_after_step det step hb
            exact Or.inl ⟨j, b, tail, hb⟩
          · obtain ⟨d, k, l, settled, cost, runa, runb⟩ := direct
            have hdl := G.rooted_steps hl runa
            have hdr := G.rooted_steps hr runb
            cases l with
            | zero =>
                have eq : G.right c = G.right d := runb.zero_eq
                have stepD : M.step (G.right d) s' := eq ▸ step
                obtain ⟨e, re, leftStep, rightStep⟩ :=
                  G.context_step d hdl hdr settled (Or.inr ⟨s', stepD⟩)
                have eq' := det stepD rightStep
                have cost' : Q.rel (1 + 0) ((1 + k) + 1) := by
                  have h := reasonable.additive cost (Q.refl 1)
                  simpa [CostOrder.converse] using h
                exact Or.inr ⟨0, (1 + k) + 1, G.right e, G.left e,
                  eq' ▸ .zero s', runa.append (.cons leftStep (.zero _)), cost',
                  ⟨_, _, Machine.Refines.refl P _,
                    ⟨e, re, G.rooted_step hdr rightStep,
                      G.rooted_step hdl leftStep, rfl, rfl⟩,
                    Machine.Refines.refl S _⟩⟩
            | succ j =>
                have tail := runb.drop_first det step
                have cost' : Q.rel (1 + j) (1 + k) := by
                  simpa [CostOrder.converse, Nat.add_comm] using cost
                exact Or.inr ⟨j, 1 + k, G.right d, G.left d, tail, runa, cost',
                  ⟨_, _, Machine.Refines.refl P _,
                    ⟨d, G.settled_remote settled, hdr, hdl, rfl, rfl⟩,
                    Machine.Refines.refl S _⟩⟩
          · obtain ⟨k, l, a, b, cost, runa, runb, quasi⟩ := quasi
            have tail := (show M.Steps (l + 1) (G.right c) b by
              simpa [Nat.add_comm] using runb).drop_first det step
            have up : M.UpTo P S G.opposite.Lifting b a := by
              obtain ⟨d, md, hdl, hdr, before, after⟩ :=
                quasi (G.rooted_steps hl runa) (G.rooted_steps hr runb)
              exact ⟨G.right d, G.left d, after.2,
                ⟨d, Or.inl md, hdr, hdl, rfl, rfl⟩,
                before.2.mono reasonable.left_in_right⟩
            exact Or.inr ⟨l, 1 + k, b, a, tail, runa, cost, up⟩
        · exact settled_case (Or.inr ⟨mode, entering⟩)
    | rewrite =>
        have notEntering : ¬ G.entering c := by
          rcases remote with notRewrite | notEntering
          · exact False.elim (notRewrite mode)
          · exact notEntering
        rcases robust c hr hl mode notEntering step with stuck | matching
        · exact Or.inl stuck
        · obtain ⟨k, l, a, b, cost, runa, runb, quasi⟩ := matching
          exact Or.inr ⟨k, l, a, b, runa, runb, cost,
            G.opposite.quasi_upTo quasi
              (G.rooted_steps (G.rooted_step hr step) runa)
              (G.rooted_steps hl runb)⟩

/-- Abstract counterpart of Theorem 6(2), conditional on graph locality. -/
theorem sufficiency_converse {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q.converse P)
    (robust : G.opposite.Robust Q P S) {s t} (related : G.Lifting s t) :
    M.Refines Q t s :=
  (G.countingSimulation_converse det reasonable safe robust).sound det reasonable
    (G.lifting_opposite.mpr related)

/-- Theorem 6's two clauses combined, at the abstract specimen level. -/
theorem equivalence {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S)
    (safe : G.InputSafe Q P) (safeConverse : G.InputSafe Q.converse P)
    (robust : G.Robust Q P S) (robustConverse : G.opposite.Robust Q P S)
    {s t} (related : G.Lifting s t) : M.Equiv Q s t :=
  ⟨G.sufficiency det reasonable safe robust related,
    G.sufficiency_converse det reasonable safeConverse robustConverse related⟩

section Contexts

variable {Interface : Type w} {Fragment : Interface → Type x}
    {Context : Interface → Type y}
    (O : Observations State Interface Fragment Context)
    (T : {i : Interface} → Fragment i → Fragment i → Prop)
    (initial_lift : ∀ {i} {a b : Fragment i}, T a b →
      ∀ (c : Context i) {s t}, O.allowed c →
        O.observe c a s → O.observe c b t → G.Lifting s t)

include initial_lift

/-- Abstract contextual forward clause. Concrete plugging, output-closure and
refocusing must establish the specimen-system laws and `initial_lift`. -/
theorem contextual_sufficiency {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q P)
    (robust : G.Robust Q P S) {i} {a b : Fragment i} (hab : T a b) :
    O.Refines M Q a b :=
  O.contextual_of_lifting M T G.Lifting initial_lift
    (G.sufficiency det reasonable safe robust) hab

theorem contextual_sufficiency_converse {Q P S : CostOrder} (det : M.Deterministic)
    (reasonable : Reasonable Q P S) (safe : G.InputSafe Q.converse P)
    (robust : G.opposite.Robust Q P S) {i} {a b : Fragment i} (hab : T a b) :
    O.Refines M Q b a := by
  intro c s t hc hs ht
  exact G.sufficiency_converse det reasonable safe robust (initial_lift hab c hc ht hs)

end Contexts

end SpecimenSystem
end Hypernets

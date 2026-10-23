import Hypernets.Simulation

/-!
The logical content of Proposition 38, factored from concrete graph plugging.
`observe` is a relation because plugging and initialization may be partial.
Its indices ensure that only fragments with a common interface are compared.
The concrete hypernet implementation must supply this observation relation and
prove that its initial states belong to contextual lifting.
-/

namespace Hypernets

universe u v w x

structure Observations (State : Type u) (Interface : Type v)
    (Fragment : Interface → Type w) (Context : Interface → Type x) where
  allowed : {i : Interface} → Context i → Prop
  observe : {i : Interface} → Context i → Fragment i → State → Prop

namespace Observations

variable {State : Type u} {Interface : Type v}
    {Fragment : Interface → Type w} {Context : Interface → Type x}
    (O : Observations State Interface Fragment Context) (M : Machine State)

def Refines (Q : CostOrder) {i : Interface} (a b : Fragment i) : Prop :=
  ∀ (c : Context i) ⦃s t⦄, O.allowed c → O.observe c a s → O.observe c b t →
    M.Refines Q s t

def Equiv (Q : CostOrder) {i : Interface} (a b : Fragment i) : Prop :=
  O.Refines M Q a b ∧ O.Refines M Q b a

/-- Proposition 38 (refinement): initial observations lie in the lifted relation.
The premise `initial_lift` is a graph obligation, not a soundness axiom. -/
theorem contextual_of_lifting {Q : CostOrder}
    (T : {i : Interface} → Fragment i → Fragment i → Prop)
    (L : State → State → Prop)
    (initial_lift : ∀ {i} {a b : Fragment i}, T a b →
      ∀ (c : Context i) {s t}, O.allowed c →
        O.observe c a s → O.observe c b t → L s t)
    (sound : ∀ {s t}, L s t → M.Refines Q s t)
    {i} {a b : Fragment i} (hab : T a b) : O.Refines M Q a b := by
  intro c s t hc hs ht
  exact sound (initial_lift hab c hc hs ht)

theorem contextual_equiv_of_lifting {Q : CostOrder}
    (T : {i : Interface} → Fragment i → Fragment i → Prop)
    (L : State → State → Prop)
    (initial_lift : ∀ {i} {a b : Fragment i}, T a b →
      ∀ (c : Context i) {s t}, O.allowed c →
        O.observe c a s → O.observe c b t → L s t)
    (sound : ∀ {s t}, L s t → M.Equiv Q s t)
    {i} {a b : Fragment i} (hab : T a b) : O.Equiv M Q a b := by
  constructor
  · exact O.contextual_of_lifting M T L initial_lift (fun h => (sound h).1) hab
  · intro c s t hc hs ht
    exact (sound (initial_lift hab c hc ht hs)).2

end Observations
end Hypernets

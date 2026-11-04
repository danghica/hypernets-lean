import Hypernets.Copying.PropositionOperationalContexts
import Hypernets.Copying.PropositionEnvironmentWeakening

/-! Explicit binding-free contexts for adding arbitrary unused environments.
Their sole hole and actual filling isomorphisms are proved compositionally. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph BoxPullWeakening

noncomputable def extendContext {r v a d k h} (C : GraphContext r v a d k h) (s : ShareSort) :
    GraphContext r v a d (variables s k) (atoms s h) where
  graph := Translation.castInterfaces (List.append_nil _) (extended_interface s k h) (insert C.graph s)
  site := (ParallelPair.leftSite (insertionBoundary [.term] (List.replicate k .term) (List.replicate h .atom) s)
    (primitiveNet d (.weakening s)) C.site).castHost (List.append_nil _) (extended_interface s k h)
  sole := SoleHole.castHost _ _ _ (ParallelPair.leftSite_sole _ _
    (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq)) C.site C.sole)
  bindingFree := by
    apply (BindingFree.castInterfaces_iff _ _ _).mpr
    apply BindingFree.parallel
    intro b; cases b
    · exact C.bindingFree
    · exact BindingFree.of_holeFree _
        (Translation.allLabels_primitive _ _ _ (by intro m eq; cases eq))
        (Translation.allLabels_primitive _ _ _ (by intro h eq; cases eq))

noncomputable def extendContext_fill {r v a d k h} (C : GraphContext r v a d k h)
    (s : ShareSort) (G : OpenProgram r v a) :
    DeepIso ((extendContext C s).fill G).graph (extend (C.fill G).graph s) := by
  change DeepIso (plugAt ((ParallelPair.leftSite
    (insertionBoundary [.term] (List.replicate k .term) (List.replicate h .atom) s)
    (primitiveNet d (.weakening s)) C.site).castHost (List.append_nil _) (extended_interface s k h)) G.graph) _
  rw [plugAt_castHost]
  have f := Translation.castInterfaces_congr (List.append_nil _) (extended_interface s k h)
    (ParallelPair.plugAt_left (insertionBoundary [.term] (List.replicate k .term) (List.replicate h .atom) s)
      (primitiveNet d (.weakening s)) C.site G.graph)
  simp only [cast_eq_reboundary] at f
  rw [cast_eq_reboundary]
  exact f

noncomputable def emptyContext (d : Nat) : GraphContext d 0 0 d 0 0 where
  graph := (ContextTranslation.hole d 0 0 0).2
  site := ContextTranslation.holeSite d 0 0 0
  sole := ContextTranslation.holeSite_sole d 0 0 0
  bindingFree := Examples.hole_bindingFree d _

noncomputable def variableContext (d : Nat) : (k : Nat) → GraphContext d 0 0 d k 0
  | 0 => emptyContext d
  | k+1 => extendContext (variableContext d k) .term

noncomputable def ambientContext (d k : Nat) : (h : Nat) → GraphContext d 0 0 d k h
  | 0 => variableContext d k
  | h+1 => extendContext (ambientContext d k h) .atom

noncomputable def variableContext_fill {d} (G : OpenProgram d 0 0) (k : Nat) :
    DeepIso ((variableContext d k).fill G).graph (addVariables G.graph k) := by
  induction k with
  | zero => exact ContextTranslation.hole_filling 0 G.graph
  | succ k ih => exact (extendContext_fill _ .term G).trans (extend_congr ih .term)

noncomputable def ambientContext_fill {d} (G : OpenProgram d 0 0) (k h : Nat) :
    DeepIso ((ambientContext d k h).fill G).graph (ambient G.graph k h) := by
  induction h with
  | zero => exact variableContext_fill G k
  | succ h ih => exact (extendContext_fill _ .atom G).trans (extend_congr ih .atom)

/-- No new primitive kind is introduced except the two genuine weakenings. -/
theorem ambient_allLabels (P : Primitive → Prop) {d} (G : Hypernet d [.term] [])
    (g : AllLabels P G) (term : P (.weakening .term)) (atom : P (.weakening .atom)) (k h : Nat) :
    AllLabels P (ambient G k h) := by
  have vars : ∀ k, AllLabels P (addVariables (h := 0) G k) := by
    intro k; induction k with
    | zero => exact g
    | succ k ih => exact (extend_allLabels _ _ _).mpr ⟨ih,term⟩
  induction h with
  | zero => exact vars k
  | succ h ih => exact (extend_allLabels _ _ _).mpr ⟨ih,atom⟩

def ambientProgram {d} (G : OpenProgram d 0 0) (k h : Nat) : OpenProgram d k h where
  graph := ambient G.graph k h
  focusFree := ambient_allLabels _ G.graph G.focusFree (by intro m eq; cases eq) (by intro m eq; cases eq) k h
  holeFree := ambient_allLabels _ G.graph G.holeFree (by intro h eq; cases eq) (by intro h eq; cases eq) k h

/-- Closed contextual equivalences lift to all finite unused environments via
an actual sole-hole binding-free context, not an assumed weakening congruence. -/
theorem ambient_equiv {d} (G H : OpenProgram d 0 0)
    (rel : Combined.execution.Equiv CostOrder.any G H) (k h : Nat) :
    Combined.execution.Equiv CostOrder.any (ambientProgram G k h) (ambientProgram H k h) :=
  Proposition12_2.context_equiv (ambientContext d k h) G H _ _ rel
    (ambientContext_fill G k h) (ambientContext_fill H k h)
end Hypernets.Copying.Weakening

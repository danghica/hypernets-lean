import Hypernets.Copying.SingleHoleAssembly
import Hypernets.Copying.BindingTranslation

/-! The literal Figure-16 context graph has exactly its annotated hole,
including through boxes, sharing distributors and depth padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SingleHole
open Graph

theorem pair_left {d k a} (h : Hole)
    {G H : Hypernet d [.term] (environmentInterface k a)}
    (g : SingleHole h G) (hf : HoleFree H) : SingleHole h (Translation.pair G H) := by
  apply (castInterfaces_iff _ _ _ _).mpr
  apply parallel _ _ _ h false g
  intro b ne
  cases b with
  | false => exact False.elim (ne rfl)
  | true => exact hf

theorem pair_right {d k a} (h : Hole)
    {G H : Hypernet d [.term] (environmentInterface k a)}
    (gf : HoleFree G) (one : SingleHole h H) : SingleHole h (Translation.pair G H) := by
  apply (castInterfaces_iff _ _ _ _).mpr
  apply parallel _ _ _ h true one
  intro b ne
  cases b with
  | true => exact False.elim (ne rfl)
  | false => exact gf

theorem operation_holeFree (d : Nat) (o : Operation) : HoleFree (primitiveNet d (.operation o)) :=
  Translation.language_holeFree (Translation.allLabels_primitive _ _ _ trivial)

theorem abstraction {d k a} (h : Hole)
    {G : Hypernet d [.term] (environmentInterface (k+1) a)}
    (g : SingleHole h G) : SingleHole h (Translation.abstraction G) := by
  apply serial_left h
  · apply serial_right h (operation_holeFree _ _)
    apply box h
    exact (castInterfaces_iff _ _ _ _).mpr g
  · exact Translation.language_holeFree (Translation.singleUse_language _ _ _)

theorem unary {d k a} (h : Hole) (o : Unary)
    {G : Hypernet d [.term] (environmentInterface k a)}
    (g : SingleHole h G) : SingleHole h (Translation.unary o G) := by
  apply serial_left h
  · exact serial_right h (operation_holeFree _ _) g
  · exact Translation.language_holeFree (Translation.singleUse_language _ _ _)

theorem application {d k a} (h : Hole)
    {G H : Hypernet d [.term] (environmentInterface k a)}
    (one : SingleHole h (Translation.pair G H)) : SingleHole h (Translation.application G H) := by
  apply serial_left h
  · exact serial_right h (operation_holeFree _ _) one
  · exact Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _)

theorem binary {d k a} (h : Hole) (o : Binary)
    {G H : Hypernet d [.term] (environmentInterface k a)}
    (one : SingleHole h (Translation.pair G H)) : SingleHole h (Translation.binary o G H) := by
  apply serial_left h
  · exact serial_right h (operation_holeFree _ _) one
  · exact Translation.language_holeFree (Translation.environmentDistributor_language _ _ _ _)

/-- A constructor context preserves the exact named-hole inventory of any
argument graph with one hole. The fixed subterms contribute no holes. -/
theorem context_apply {v a k b} (h : Hole) (C : TermContext v a k b)
    (G : ContextTranslation.ScopedGraph v a) (g : SingleHole h G.2) :
    SingleHole h (ContextTranslation.apply C G).2 := by
  induction C with
  | hole => exact g
  | lam C ih => exact abstraction h ih
  | unary o C ih => exact unary h o ih
  | appLeft C u ih =>
    apply application h
    exact pair_left h ((padTo_iff _ _ _ _).mpr ih)
      ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u))
  | appRight u C ih =>
    apply application h
    exact pair_right h ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u))
      ((padTo_iff _ _ _ _).mpr ih)
  | binaryLeft o C u ih =>
    apply binary h o
    exact pair_left h ((padTo_iff _ _ _ _).mpr ih)
      ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u))
  | binaryRight o u C ih =>
    apply binary h o
    exact pair_right h ((Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u))
      ((padTo_iff _ _ _ _).mpr ih)

/-- The actual translated context contains exactly its annotated hole. -/
theorem context_graph {v a k b} (C : TermContext v a k b) (d name : Nat) :
    SingleHole ⟨name,[.term],environmentInterface v a⟩ (ContextTranslation.graph C d name).2 :=
  context_apply _ C _ (corolla d _)

/-- An actual addressed, sole-hole and binding-free certificate for every
translated lambda-context. No conditional graph-realisation interface is used. -/
theorem context_certificate {v a k b} (C : TermContext v a k b) (d name : Nat) :
    ∃ r, ∃ s : Site (ContextTranslation.graph C d name).2 r [.term] (environmentInterface v a),
      SoleHole s ∧ BindingFree (ContextTranslation.graph C d name).2 := by
  obtain ⟨r,s,sole⟩ := site _ _ _ (context_graph C d name)
  exact ⟨r,s,sole,BindingFree.context_graph C d name⟩
end Hypernets.Copying.SingleHole

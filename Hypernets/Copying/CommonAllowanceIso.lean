import Hypernets.Copying.PaddingConstructors

/-! Structural comparison at a common sufficient allowance, without changing
any translated graph or identifying graphs by a new observational definition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContextTranslation

/-- The two original graphs become recursively isomorphic at this allowance. -/
structure AgreeAt {k h} (G H : ScopedGraph k h) (N : Nat) : Prop where
  left : G.1 ≤ N
  right : H.1 ≤ N
  related : Nonempty (DeepIso (Translation.padTo N left G.2) (Translation.padTo N right H.2))

namespace AgreeAt

theorem widen {k h} {G H : ScopedGraph k h} {N M : Nat} (f : AgreeAt G H N) (bound : N ≤ M) :
    AgreeAt G H M := by
  obtain ⟨gN,hN,⟨iso⟩⟩ := f
  refine ⟨Nat.le_trans gN bound,Nat.le_trans hN bound,?_⟩
  have lifted := Translation.padTo_congr M bound iso
  simpa only [Translation.padTo_trans] using Nonempty.intro lifted

theorem refl {k h} (G : ScopedGraph k h) (N : Nat) (bound : G.1 ≤ N) : AgreeAt G G N :=
  ⟨bound,bound,⟨DeepIso.refl _⟩⟩

theorem symm {k h} {G H : ScopedGraph k h} {N} (f : AgreeAt G H N) : AgreeAt H G N := by
  obtain ⟨gN,hN,⟨f⟩⟩ := f
  exact ⟨hN,gN,⟨f.symm⟩⟩

theorem trans {k h} {G H K : ScopedGraph k h} {N} (f : AgreeAt G H N) (g : AgreeAt H K N) :
    AgreeAt G K N := by
  obtain ⟨gN,hN,⟨f⟩⟩ := f
  obtain ⟨_,kN,⟨g⟩⟩ := g
  exact ⟨gN,kN,⟨f.trans g⟩⟩

theorem unary {k h} (o : Unary) {G H : ScopedGraph k h} {N} (f : AgreeAt G H N) :
    AgreeAt (ContextTranslation.unary o G) (ContextTranslation.unary o H) N := by
  obtain ⟨gN,hN,⟨f⟩⟩ := f
  exact ⟨gN,hN,⟨(Padding.unary_to o G.2 N gN).trans
    ((Translation.unary_congr o f).trans (Padding.unary_to o H.2 N hN).symm)⟩⟩

theorem abstraction {k h} {G H : ScopedGraph (k+1) h} {N} (f : AgreeAt G H N) :
    AgreeAt (ContextTranslation.abstraction G) (ContextTranslation.abstraction H) (N+1) := by
  obtain ⟨gN,hN,⟨f⟩⟩ := f
  exact ⟨Nat.succ_le_succ gN,Nat.succ_le_succ hN,⟨(Padding.abstraction_to G.2 N gN).trans
    ((Translation.abstraction_congr f).trans (Padding.abstraction_to H.2 N hN).symm)⟩⟩
end AgreeAt

/-- Padding the original application interpreter collapses its intermediate
maximum to the requested common allowance, retaining both distributors. -/
noncomputable def application_to {k h} (G H : ScopedGraph k h) (N : Nat)
    (gN : G.1 ≤ N) (hN : H.1 ≤ N) :
    DeepIso (Translation.padTo N (Nat.max_le.mpr ⟨gN,hN⟩) (application G H).2)
      (Translation.application (Translation.padTo N gN G.2) (Translation.padTo N hN H.2)) := by
  have f := Padding.application_to (Translation.padTo _ (Nat.le_max_left G.1 H.1) G.2)
    (Translation.padTo _ (Nat.le_max_right G.1 H.1) H.2) N (Nat.max_le.mpr ⟨gN,hN⟩)
  simpa only [application,Translation.padTo_trans] using f

noncomputable def binary_to {k h} (o : Binary) (G H : ScopedGraph k h) (N : Nat)
    (gN : G.1 ≤ N) (hN : H.1 ≤ N) :
    DeepIso (Translation.padTo N (Nat.max_le.mpr ⟨gN,hN⟩) (binary o G H).2)
      (Translation.binary o (Translation.padTo N gN G.2) (Translation.padTo N hN H.2)) := by
  have f := Padding.binary_to o (Translation.padTo _ (Nat.le_max_left G.1 H.1) G.2)
    (Translation.padTo _ (Nat.le_max_right G.1 H.1) H.2) N (Nat.max_le.mpr ⟨gN,hN⟩)
  simpa only [binary,Translation.padTo_trans] using f

namespace AgreeAt

theorem application {k h} {G G' H H' : ScopedGraph k h} {N}
    (f : AgreeAt G G' N) (g : AgreeAt H H' N) :
    AgreeAt (ContextTranslation.application G H) (ContextTranslation.application G' H') N := by
  obtain ⟨gN,gN',⟨f⟩⟩ := f
  obtain ⟨hN,hN',⟨g⟩⟩ := g
  exact ⟨Nat.max_le.mpr ⟨gN,hN⟩,Nat.max_le.mpr ⟨gN',hN'⟩,
    ⟨(application_to G H N gN hN).trans
      ((Translation.application_congr f g).trans (application_to G' H' N gN' hN').symm)⟩⟩

theorem binary {k h} (o : Binary) {G G' H H' : ScopedGraph k h} {N}
    (f : AgreeAt G G' N) (g : AgreeAt H H' N) :
    AgreeAt (ContextTranslation.binary o G H) (ContextTranslation.binary o G' H') N := by
  obtain ⟨gN,gN',⟨f⟩⟩ := f
  obtain ⟨hN,hN',⟨g⟩⟩ := g
  exact ⟨Nat.max_le.mpr ⟨gN,hN⟩,Nat.max_le.mpr ⟨gN',hN'⟩,
    ⟨(binary_to o G H N gN hN).trans
      ((Translation.binary_congr o f g).trans (binary_to o G' H' N gN' hN').symm)⟩⟩
end AgreeAt

/-- Existence of a sufficient common allowance with an actual recursive isomorphism. -/
def CommonIso {k h} (G H : ScopedGraph k h) : Prop := ∃ N, AgreeAt G H N

namespace CommonIso

theorem refl {k h} (G : ScopedGraph k h) : CommonIso G G := ⟨G.1,AgreeAt.refl G _ (Nat.le_refl _)⟩

theorem symm {k h} {G H : ScopedGraph k h} (f : CommonIso G H) : CommonIso H G := by
  obtain ⟨N,f⟩ := f; exact ⟨N,f.symm⟩

theorem trans {k h} {G H K : ScopedGraph k h} (f : CommonIso G H) (g : CommonIso H K) : CommonIso G K := by
  obtain ⟨N,f⟩ := f; obtain ⟨M,g⟩ := g
  exact ⟨max N M,(f.widen (Nat.le_max_left _ _)).trans (g.widen (Nat.le_max_right _ _))⟩

theorem ofScoped {k h} {G H : ScopedGraph k h} (f : ScopedIso G H) : CommonIso G H := by
  refine ⟨max G.1 H.1,Nat.le_max_left _ _,Nat.le_max_right _ _,?_⟩
  exact f.padTo _ _ _

theorem unary {k h} (o : Unary) {G H : ScopedGraph k h} (f : CommonIso G H) :
    CommonIso (ContextTranslation.unary o G) (ContextTranslation.unary o H) := by
  obtain ⟨N,f⟩ := f; exact ⟨N,f.unary o⟩

theorem abstraction {k h} {G H : ScopedGraph (k+1) h} (f : CommonIso G H) :
    CommonIso (ContextTranslation.abstraction G) (ContextTranslation.abstraction H) := by
  obtain ⟨N,f⟩ := f; exact ⟨N+1,f.abstraction⟩

theorem application {k h} {G G' H H' : ScopedGraph k h} (f : CommonIso G G') (g : CommonIso H H') :
    CommonIso (ContextTranslation.application G H) (ContextTranslation.application G' H') := by
  obtain ⟨N,f⟩ := f; obtain ⟨M,g⟩ := g
  exact ⟨max N M,(f.widen (Nat.le_max_left _ _)).application (g.widen (Nat.le_max_right _ _))⟩

theorem binary {k h} (o : Binary) {G G' H H' : ScopedGraph k h} (f : CommonIso G G') (g : CommonIso H H') :
    CommonIso (ContextTranslation.binary o G H) (ContextTranslation.binary o G' H') := by
  obtain ⟨N,f⟩ := f; obtain ⟨M,g⟩ := g
  exact ⟨max N M,(f.widen (Nat.le_max_left _ _)).binary o (g.widen (Nat.le_max_right _ _))⟩

/-- Every original annotated context respects common-allowance structural comparison. -/
theorem apply {v a k h} (C : TermContext v a k h) {G H : ScopedGraph v a} (f : CommonIso G H) :
    CommonIso (ContextTranslation.apply C G) (ContextTranslation.apply C H) := by
  induction C with
  | hole => exact f
  | lam C ih => exact ih.abstraction
  | unary o C ih => exact ih.unary o
  | appLeft C u ih => exact ih.application (refl _)
  | appRight u C ih => exact (refl _).application ih
  | binaryLeft o C u ih => exact ih.binary o (refl _)
  | binaryRight o u C ih => exact (refl _).binary o ih

/-- The original graph and its padded representation agree at the larger allowance. -/
theorem padTo {k h} (G : ScopedGraph k h) (N : Nat) (bound : G.1 ≤ N) :
    CommonIso G ⟨N,Translation.padTo N bound G.2⟩ := by
  refine ⟨N,bound,Nat.le_refl _,?_⟩
  rw [Translation.padTo_self]
  exact ⟨DeepIso.refl _⟩
end CommonIso
end Hypernets.Copying.ContextTranslation

import Hypernets.Copying.PaddingComposition
import Hypernets.Copying.CertifiedContexts

/-! Actual addressed filling for the entire original annotated context grammar. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContextTranslation
namespace ScopedIso

theorem application {k h} {G G' H H' : ScopedGraph k h}
    (f : ScopedIso G G') (g : ScopedIso H H') :
    ScopedIso (ContextTranslation.application G H) (ContextTranslation.application G' H') := by
  obtain ⟨d,G⟩ := G; obtain ⟨e,G'⟩ := G'; obtain ⟨r,H⟩ := H; obtain ⟨q,H'⟩ := H'
  obtain ⟨eq,⟨f⟩⟩ := f; obtain ⟨eq',⟨g⟩⟩ := g
  change d = e at eq; change r = q at eq'
  subst e; subst q
  exact ofIso (Translation.application_congr (Translation.padTo_congr _ _ f)
    (Translation.padTo_congr _ _ g))

theorem binary {k h} (o : Binary) {G G' H H' : ScopedGraph k h}
    (f : ScopedIso G G') (g : ScopedIso H H') :
    ScopedIso (ContextTranslation.binary o G H) (ContextTranslation.binary o G' H') := by
  obtain ⟨d,G⟩ := G; obtain ⟨e,G'⟩ := G'; obtain ⟨r,H⟩ := H; obtain ⟨q,H'⟩ := H'
  obtain ⟨eq,⟨f⟩⟩ := f; obtain ⟨eq',⟨g⟩⟩ := g
  change d = e at eq; change r = q at eq'
  subst e; subst q
  exact ofIso (Translation.binary_congr o (Translation.padTo_congr _ _ f)
    (Translation.padTo_congr _ _ g))
end ScopedIso

/-- Every original context respects recursive isomorphism at the same input
allowance, including its prescribed common-depth choices. -/
theorem apply_iso {v a k h} (C : TermContext v a k h) {G H : ScopedGraph v a}
    (f : ScopedIso G H) : ScopedIso (apply C G) (apply C H) := by
  induction C with
  | hole => exact f
  | lam C ih => exact ScopedIso.abstraction ih
  | unary o C ih => exact ScopedIso.unary o ih
  | appLeft C u ih => exact ScopedIso.application ih (ScopedIso.refl _)
  | appRight u C ih => exact ScopedIso.application (ScopedIso.refl _) ih
  | binaryLeft o C u ih => exact ScopedIso.binary o ih (ScopedIso.refl _)
  | binaryRight o u C ih => exact ScopedIso.binary o (ScopedIso.refl _) ih

/-- A single certified address reconstructs every filling of an original
annotated context. The accumulated padding is chosen from the context and
input allowance before the argument graph is supplied. -/
theorem context_filling {v a k h} (C : TermContext v a k h) (d name : Nat) :
    ∃ n, ∃ s : Site (graph C d name).2 (d+n) [.term] (environmentInterface v a),
      SoleHole s ∧ ∀ A : Hypernet d [.term] (environmentInterface v a),
        ScopedIso ⟨(graph C d name).1,plugAt s (Translation.pad d n A)⟩ (apply C ⟨d,A⟩) := by
  induction C with
  | hole =>
    exact ⟨0,holeSite d name v a,holeSite_sole d name v a,
      fun A => ScopedIso.ofIso (hole_filling name A)⟩
  | lam C ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    refine ⟨n,Translation.abstractionSite s,Translation.abstractionSite_sole s sole,?_⟩
    intro A
    exact (ScopedIso.ofIso (Translation.abstraction_filling s _)).trans
      (ScopedIso.abstraction (law A))
  | unary o C ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    refine ⟨n,Translation.unarySite o s,Translation.unarySite_sole o s sole,?_⟩
    intro A
    exact (ScopedIso.ofIso (Translation.unary_filling o s _)).trans
      (ScopedIso.unary o (law A))
  | appLeft C u ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    let N := max (graph C d name).1 (Translation.depth u)
    let bound : (graph C d name).1 ≤ N := Nat.le_max_left _ _
    let fixed := Translation.padTo N (Nat.le_max_right _ _) (Translation.term u)
    have free : HoleFree fixed :=
      (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u)
    let lifted := Padding.toSite s N bound
    refine ⟨n+(N-(graph C d name).1),Translation.applicationLeftSite fixed lifted,
      Translation.applicationLeftSite_sole fixed free lifted (Padding.toSite_sole s sole N bound),?_⟩
    intro A
    have f := (Translation.applicationLeft_filling fixed lifted (Translation.pad d _ A)).trans
      (Translation.application_congr (Padding.to_filling s A N bound) (DeepIso.refl fixed))
    exact (ScopedIso.ofIso f).trans
      (ScopedIso.application (law A) (ScopedIso.refl (ofTerm u)))
  | appRight u C ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    let N := max (Translation.depth u) (graph C d name).1
    let bound : (graph C d name).1 ≤ N := Nat.le_max_right _ _
    let fixed := Translation.padTo N (Nat.le_max_left _ _) (Translation.term u)
    have free : HoleFree fixed :=
      (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u)
    let lifted := Padding.toSite s N bound
    refine ⟨n+(N-(graph C d name).1),Translation.applicationRightSite fixed lifted,
      Translation.applicationRightSite_sole fixed free lifted (Padding.toSite_sole s sole N bound),?_⟩
    intro A
    have f := (Translation.applicationRight_filling fixed lifted (Translation.pad d _ A)).trans
      (Translation.application_congr (DeepIso.refl fixed) (Padding.to_filling s A N bound))
    exact (ScopedIso.ofIso f).trans
      (ScopedIso.application (ScopedIso.refl (ofTerm u)) (law A))
  | binaryLeft o C u ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    let N := max (graph C d name).1 (Translation.depth u)
    let bound : (graph C d name).1 ≤ N := Nat.le_max_left _ _
    let fixed := Translation.padTo N (Nat.le_max_right _ _) (Translation.term u)
    have free : HoleFree fixed :=
      (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u)
    let lifted := Padding.toSite s N bound
    refine ⟨n+(N-(graph C d name).1),Translation.binaryLeftSite o fixed lifted,
      Translation.binaryLeftSite_sole o fixed free lifted (Padding.toSite_sole s sole N bound),?_⟩
    intro A
    have f := (Translation.binaryLeft_filling o fixed lifted (Translation.pad d _ A)).trans
      (Translation.binary_congr o (Padding.to_filling s A N bound) (DeepIso.refl fixed))
    exact (ScopedIso.ofIso f).trans
      (ScopedIso.binary o (law A) (ScopedIso.refl (ofTerm u)))
  | binaryRight o u C ih =>
    obtain ⟨n,s,sole,law⟩ := ih
    let N := max (Translation.depth u) (graph C d name).1
    let bound : (graph C d name).1 ≤ N := Nat.le_max_right _ _
    let fixed := Translation.padTo N (Nat.le_max_left _ _) (Translation.term u)
    have free : HoleFree fixed :=
      (Translation.allLabels_padTo _ _ _ _).mpr (Translation.term_holeFree u)
    let lifted := Padding.toSite s N bound
    refine ⟨n+(N-(graph C d name).1),Translation.binaryRightSite o fixed lifted,
      Translation.binaryRightSite_sole o fixed free lifted (Padding.toSite_sole s sole N bound),?_⟩
    intro A
    have f := (Translation.binaryRight_filling o fixed lifted (Translation.pad d _ A)).trans
      (Translation.binary_congr o (DeepIso.refl fixed) (Padding.to_filling s A N bound))
    exact (ScopedIso.ofIso f).trans
      (ScopedIso.binary o (ScopedIso.refl (ofTerm u)) (law A))

/-- Unrestricted term contexts have an actual sole, binding-free graph hole.
Filling with the suitably padded original term translation recovers the exact
translation of the filled term up to recursive isomorphism. -/
theorem context_term_filling {v a k h} (C : TermContext v a k h) (name : Nat) (t : Term v a) :
    ∃ n, ∃ s : Site (graph C (Translation.depth t) name).2 (Translation.depth t+n)
        [.term] (environmentInterface v a),
      SoleHole s ∧ BindingFree (graph C (Translation.depth t) name).2 ∧
      ScopedIso ⟨(graph C (Translation.depth t) name).1,
        plugAt s (Translation.pad (Translation.depth t) n (Translation.term t))⟩
        (ofTerm (C.fill t)) := by
  obtain ⟨n,s,sole,law⟩ := context_filling C (Translation.depth t) name
  refine ⟨n,s,sole,BindingFree.context_graph C _ name,?_⟩
  have result := law (Translation.term t)
  change ScopedIso _ (apply C (ofTerm t)) at result
  rwa [apply_ofTerm] at result
/-- The certified interface can use the very address whose filling law is
proved, with literal equality to the original translated host graph. -/
theorem context_graph_filling {v a k h} (C : TermContext v a k h) (d name : Nat) :
    ∃ n, ∃ D : GraphContext (d+n) v a (graph C d name).1 k h,
      D.graph = (graph C d name).2 ∧
      ∀ A : Hypernet d [.term] (environmentInterface v a),
        ScopedIso ⟨(graph C d name).1,plugAt D.site (Translation.pad d n A)⟩
          (apply C ⟨d,A⟩) := by
  obtain ⟨n,s,sole,law⟩ := context_filling C d name
  exact ⟨n,⟨_,s,sole,BindingFree.context_graph C d name⟩,rfl,law⟩
end Hypernets.Copying.ContextTranslation

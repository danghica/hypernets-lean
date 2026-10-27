import Hypernets.Copying.OpeningPresentationIso

/-! Complete beta-successor certificates, including the resumed token. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph Opening

structure OpeningCertificate {d I O k h} (G H : Hypernet (d+1) I O) (v : G.Vertex) (w : H.Vertex)
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) where
  matched : Match G v B
  realization : Realization matched.presentation H
  token : Port.map realization.vertices w = Port.map Sum.inl v

/-- The original local rule, with its entire body, supplies a complete certificate. -/
def local_certificate {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : OpeningCertificate (before B G) (after B G) (.input 0) (.input 0) B where
  matched := localMatch B G
  realization := opening_realization B G
  token := rfl

/-- Removing equal-interface casts reflects recursive graph isomorphism. -/
def cast_iso_reflect {d I O J K} (hi : I = J) (ho : O = K) {G H : Hypernet d I O}
    (f : DeepIso (Translation.castInterfaces hi ho G) (Translation.castInterfaces hi ho H)) : DeepIso G H := by
  cases hi; cases ho; exact f

namespace OpeningCertificate
variable {d I O k h} {G H K G' H' : Hypernet (d+1) I O} {v w}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- Renaming both sides preserves the source-relative complete successor certificate. -/
def rename (a : OpeningCertificate G H v w B) (f : DeepIso G G') (g : DeepIso H H') :
    OpeningCertificate G' H' (Port.map f.vertices.toFun v) (Port.map g.vertices.toFun w) B where
  matched := a.matched.map (Occurrence.ofIso f)
  realization := (a.realization.transport (a.matched.renamePresentation f)).rename g.symm
  token := by
    change Port.map ((f.vertices.sum (Bijection.refl _)).toFun ∘ a.realization.vertices ∘ g.vertices.invFun)
      (Port.map g.vertices.toFun w) = _
    rw [Arithmetic.Reduction.port_comp]
    have inv := (Port.bijection g.vertices).left_inv w
    change Port.map g.vertices.invFun (Port.map g.vertices.toFun w) = w at inv
    rw [Arithmetic.Reduction.port_comp,inv,a.token]
    cases v <;> rfl

/-- Matching the same source suffices: independently represented opened bodies are compared. -/
theorem coherent {u : K.Vertex} {l j} {C : Hypernet d [.term] (environmentInterface (l+1) j)}
    (a : OpeningCertificate G H v w B) (b : OpeningCertificate G K v u C) :
    Nonempty (Combined.StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  have related := a.matched.bodies_related b.matched
  cases related with
  | bodies related =>
    obtain ⟨bodyIso⟩ := related
    have raw := cast_iso_reflect rfl (by rw [Nat.add_comm k 1]) bodyIso
    have opened : DeepIso (openBody B) (openBody C) :=
      Translation.castInterfaces_congr _ _ (Padding.congr raw)
    let transported := a.realization.transport (a.matched.bodyPresentation b.matched opened)
    refine ⟨transported.stateIso b.realization ?_⟩
    change Port.map (((Bijection.refl G.Internal).sum opened.vertices).toFun ∘ a.realization.vertices) w = _
    rw [Arithmetic.Reduction.port_comp,a.token,b.token]
    cases v <;> rfl
end OpeningCertificate
end Hypernets.Copying.Application

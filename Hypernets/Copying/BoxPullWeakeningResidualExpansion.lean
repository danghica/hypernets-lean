import Hypernets.Copying.BoxPullWeakeningResidual
import Hypernets.Copying.PointedExpansion

/-! Exact expansion closure of the three-link BPullW residual. Untouched
components retain their BPullW fillings first and are unchanged during Idem. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

namespace PointedWitness
variable {T : PreTemplate}

/-- Equality transport of graph carriers changes no boundary index. -/
def castVertex {d I O} {G H : Hypernet d I O} (eq : G = H) (v : G.Vertex) : H.Vertex :=
  Port.map (cast (congrArg Net.Internal eq)) v

@[simp] theorem castVertex_refl {d I O} {G : Hypernet d I O} (v : G.Vertex) :
    castVertex rfl v = v := by cases v <;> rfl

noncomputable def cast {d I O} {G H A B : Hypernet d I O} {v w}
    (p : PointedWitness T G v H w) (left : G = A) (right : H = B) :
    PointedWitness T A (castVertex left v) B (castVertex right w) := by
  cases left; cases right
  simpa only [castVertex_refl] using p

/-- Assemble the selected pointed witness and every unchanged component's
original filling without imposing any condition on the enclosing incidences. -/
noncomputable def expandSelected {d I O} (C : Hypernet d I O)
    (G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (G e).Vertex} {w : (H e).Vertex}
    (p : PointedWitness T (G e) v (H e) w)
    (others : ∀ b, b ≠ e → FillingWitness T (G b) (H b)) :
    PointedWitness T (C.expand G) (Net.Expansion.insert C G e v)
      (C.expand H) (Net.Expansion.insert C H e w) := by
  classical
  let cert : ∀ b, FillingWitness T (G b) (H b) := fun b =>
    if eq : b = e then eq.symm ▸ p.filling else others b eq
  have selected : cert e = p.filling := by simp [cert]
  let q := _root_.cast (congrArg (fun t => t.context.Vertex) selected.symm) p.point
  have pointed := expandAt C cert e q
  have leftCast (A B : FillingWitness T (G e) (H e)) (eq : A = B) (x : B.context.Vertex) :
      A.leftPosition (.search,_root_.cast (congrArg (fun t => t.context.Vertex) eq.symm) x) =
        B.leftPosition (.search,x) := by cases eq; rfl
  have rightCast (A B : FillingWitness T (G e) (H e)) (eq : A = B) (x : B.context.Vertex) :
      A.rightPosition (.search,_root_.cast (congrArg (fun t => t.context.Vertex) eq.symm) x) =
        B.rightPosition (.search,x) := by cases eq; rfl
  have lt := (leftCast _ _ selected p.point).trans (Prod.ext rfl p.left : p.filling.leftPosition (.search,p.point) = (.search,v))
  have rt := (rightCast _ _ selected p.point).trans (Prod.ext rfl p.right : p.filling.rightPosition (.search,p.point) = (.search,w))
  simpa only [q,lt,rt] using pointed
end PointedWitness

namespace Residual
/-- The active three-link residual expands through an arbitrary original frame.
Every other BPullW occurrence is retained in the first link; the correction
links use only reflexive Idem witnesses on those other components. -/
noncomputable def expandSelected {d I O} (C : Hypernet d I O)
    (G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (G e).Vertex} {w : (H e).Vertex} (p : Residual (G e) v (H e) w)
    (others : ∀ b, b ≠ e → FillingWitness template (G b) (H b)) :
    Residual (C.expand G) (Net.Expansion.insert C G e v)
      (C.expand H) (Net.Expansion.insert C H e w) := by
  let M := BoxPermutation.PointedFilling.replace C H e p.middle
  let N := BoxPermutation.PointedFilling.replace C H e p.next
  have middle : p.middle = M e := (BoxPermutation.PointedFilling.replace_selected C H e p.middle).symm
  have next : p.next = N e := (BoxPermutation.PointedFilling.replace_selected C H e p.next).symm
  let p0 := p.paired.cast rfl middle
  let p1 := p.first.cast middle next
  let p2 := p.second.cast next rfl
  have other0 (b) (ne : b ≠ e) : FillingWitness template (G b) (M b) := by
    simpa only [M,BoxPermutation.PointedFilling.replace_other C H e p.middle b ne] using others b ne
  have other1 (b) (ne : b ≠ e) : FillingWitness ContractionIdempotence.template (M b) (N b) := by
    simpa only [M,N,BoxPermutation.PointedFilling.replace_other C H e p.middle b ne,
      BoxPermutation.PointedFilling.replace_other C H e p.next b ne] using
        FillingWitness.refl (T := ContractionIdempotence.template) (H b) (others b ne).focusFree.2
  have other2 (b) (ne : b ≠ e) : FillingWitness ContractionIdempotence.template (N b) (H b) := by
    simpa only [N,BoxPermutation.PointedFilling.replace_other C H e p.next b ne] using
      FillingWitness.refl (T := ContractionIdempotence.template) (H b) (others b ne).focusFree.2
  refine ⟨C.expand M,Net.Expansion.insert C M e (PointedWitness.castVertex middle p.point),
    C.expand N,Net.Expansion.insert C N e (PointedWitness.castVertex next p.nextPoint),?_,?_,?_⟩
  · have q := PointedWitness.expandSelected C G M e p0 other0
    simpa only [PointedWitness.castVertex_refl] using q
  · exact PointedWitness.expandSelected C M N e p1 other1
  · have q := PointedWitness.expandSelected C N H e p2 other2
    simpa only [PointedWitness.castVertex_refl] using q


/-- A selected actual rewrite and its three-link residual lift together through
a whole simultaneous expansion. The complement is the original derivation's
finite frame, with every other contribution explicitly retained. -/
theorem assemble {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (F e).Vertex} {w : (K e).Vertex}
    {H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {z : H.Vertex}
    (step : Rewrite (F e) v H z) (p : Residual (K e) w H z)
    (others : ∀ b, b ≠ e → FillingWitness template (K b) (F b)) :
    ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
      Nonempty (Residual (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
  let J := BoxPermutation.PointedFilling.replace C F e H
  have build (H' : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (eq : J e = H')
      (z' : H'.Vertex) (s : Rewrite (F e) v H' z') (p' : Residual (K e) w H' z') :
      ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
        Nonempty (Residual (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
    subst H'
    have other (b) (ne : b ≠ e) : FillingWitness template (K b) (J b) := by
      simpa only [J,BoxPermutation.PointedFilling.replace_other C F e H b ne] using others b ne
    exact ⟨C.expand J,Net.Expansion.insert C J e z',
      .expand C F J e (fun b ne => (BoxPermutation.PointedFilling.replace_other C F e H b ne).symm) s,
      ⟨expandSelected C K J e p' other⟩⟩
  exact build H (BoxPermutation.PointedFilling.replace_selected C F e H) z step p
end Residual
end Hypernets.Copying.BoxPullWeakening

import Hypernets.Copying.ExpandedRewrite

/-! Exact expansion of one matched rewrite together with every residual component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined

namespace PointedFilling
/-- Change just one member of a dependent filling family. -/
noncomputable def replace {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (b : C.Edge) :
    Hypernet d ((alphabet d).signature.input (C.edgeLabel b))
      ((alphabet d).signature.output (C.edgeLabel b)) := by
  classical
  exact if eq : b = e then eq.symm ▸ H else F b

@[simp] theorem replace_selected {d I O} (C : Hypernet d I O) (F) (e) (H) :
    replace C F e H e = H := by
  classical
  simp [replace]

theorem replace_other {d I O} (C : Hypernet d I O) (F) (e) (H) (b) (ne : b ≠ e) :
    replace C F e H b = F b := by
  classical
  simp [replace,ne]

/-- Lift an actual selected step and its pointed residual through a whole
simultaneous expansion. The other residual components need not be isomorphic. -/
theorem assemble {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    {v : (F e).Vertex} {w : (K e).Vertex}
    {H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} {z : H.Vertex}
    (step : Rewrite (F e) v H z) (p : PointedFilling (K e) w H z)
    (others : ∀ b, b ≠ e → FillingWitness template (K b) (F b)) :
    ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
      Nonempty (PointedFilling (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
  classical
  let J := replace C F e H
  have build (H' : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (eq : J e = H')
      (z' : H'.Vertex) (s : Rewrite (F e) v H' z')
      (p' : PointedFilling (K e) w H' z') :
      ∃ Q q, Rewrite (C.expand F) (Net.Expansion.insert C F e v) Q q ∧
        Nonempty (PointedFilling (C.expand K) (Net.Expansion.insert C K e w) Q q) := by
    subst H'
    let cert : ∀ b, FillingWitness template (K b) (J b) := fun b =>
      if eq : b = e then eq.symm ▸ p'.filling else
        by
          have h := others b eq
          simpa only [J,replace_other C F e H b eq] using h
    have selectedEq : cert e = p'.filling := by simp [cert]
    have pointed := expandAt C cert e (cast (congrArg (fun t => t.context.Vertex) selectedEq.symm) p'.point)
    have leftCast (A B : FillingWitness template (K e) (J e)) (eq : A = B) (x : B.context.Vertex) :
        A.leftPosition (.search,cast (congrArg (fun t => t.context.Vertex) eq.symm) x) =
          B.leftPosition (.search,x) := by cases eq; rfl
    have rightCast (A B : FillingWitness template (K e) (J e)) (eq : A = B) (x : B.context.Vertex) :
        A.rightPosition (.search,cast (congrArg (fun t => t.context.Vertex) eq.symm) x) =
          B.rightPosition (.search,x) := by cases eq; rfl
    have lt := (leftCast _ _ selectedEq p'.point).trans (Prod.ext rfl p'.left : p'.filling.leftPosition (.search,p'.point) = (.search,w))
    have rt := (rightCast _ _ selectedEq p'.point).trans (Prod.ext rfl p'.right : p'.filling.rightPosition (.search,p'.point) = (.search,z'))
    refine ⟨C.expand J, Net.Expansion.insert C J e z',
      .expand C F J e (fun b ne => (replace_other C F e H b ne).symm) s, ?_⟩
    simpa only [lt,rt] using Nonempty.intro pointed
  exact build H (replace_selected C F e H) z step p
end PointedFilling
end Hypernets.Copying.BoxPermutation

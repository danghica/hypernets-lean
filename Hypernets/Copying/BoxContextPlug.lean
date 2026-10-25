import Hypernets.Copying.SerialDeepPlug
import Hypernets.Copying.UnaryPlug

/-! Exact addressed filling through boxes and the unchanged abstraction clause. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Transport the outer interface of a host without changing the local address. -/
def Site.castHost {d I O} {G : Hypernet d I O} {r U V J K}
    (hi : I = J) (ho : O = K) (s : Site G r U V) :
    Site (Translation.castInterfaces hi ho G) r U V := by cases hi; cases ho; exact s

theorem plugAt_castHost {d I O} {G : Hypernet d I O} {r U V J K}
    (hi : I = J) (ho : O = K) (s : Site G r U V) (A : Hypernet r U V) :
    plugAt (s.castHost hi ho) A = Translation.castInterfaces hi ho (plugAt s A) := by
  cases hi; cases ho; rfl

/-- Follow an address through a newly enclosing box. -/
def boxSite {d bound free atoms}
    {G : Hypernet d [.term] (environmentInterface (bound+free) atoms)}
    {r U V} (s : Site G r U V) : Site (box (bound := bound) (freeVariables := free) G) r U V := by
  exact .inside (0 : Fin 1) ⟨bound,free,atoms,G⟩ rfl s

/-- Filling beneath the new box preserves that box and changes only its body. -/
noncomputable def box_filling {d bound free atoms}
    {G : Hypernet d [.term] (environmentInterface (bound+free) atoms)}
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    Net.Iso (plugAt (boxSite (bound := bound) (free := free) s) A)
      (box (bound := bound) (freeVariables := free) (plugAt s A)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := nomatch v
  edge_label e := by
    classical
    change Fin 1 at e
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e
    simp [boxSite,plugAt,replaceBox,Net.relabelEdges]
  source e := by simp [boxSite,plugAt,replaceBox,Net.relabelEdges,box,Net.corolla,Bijection.refl,nextAlphabet]
  target e := by simp [boxSite,plugAt,replaceBox,Net.relabelEdges,box,Net.corolla,Bijection.refl,nextAlphabet]

/-- Recursive body isomorphisms lift through a box with its interface fixed. -/
def box_congr {d bound free atoms}
    {G H : Hypernet d [.term] (environmentInterface (bound+free) atoms)}
    (f : DeepIso G H) :
    DeepIso (box (bound := bound) (freeVariables := free) G)
      (box (bound := bound) (freeVariables := free) H) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := nomatch v
  edge_label _ := BoxRelated.bodies ⟨f⟩
  source e := by simp [box,Net.corolla,Bijection.refl,nextAlphabet]
  target e := by simp [box,Net.corolla,Bijection.refl,nextAlphabet]

/-- Interface equality transport preserves a sole-hole certificate. -/
theorem SoleHole.castHost {d I O} {G : Hypernet d I O} {r U V J K}
    (hi : I = J) (ho : O = K) (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (s.castHost hi ho) := by cases hi; cases ho; exact sole

/-- Enclosing a sole hole in a singleton box introduces no other holes. -/
theorem boxSite_sole {d bound free atoms}
    {G : Hypernet d [.term] (environmentInterface (bound+free) atoms)}
    {r U V} (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (boxSite (bound := bound) (free := free) s) := by
  refine ⟨sole,?_⟩
  intro e ne
  exact False.elim (ne (Fin.ext (by omega)))

namespace Translation
/-- Equality casts of outer interfaces preserve recursive isomorphism. -/
def castInterfaces_congr {d I O J K} (hi : I = J) (ho : O = K)
    {G H : Hypernet d I O} (f : DeepIso G H) :
    DeepIso (castInterfaces hi ho G) (castInterfaces hi ho H) := by
  cases hi; cases ho; exact f

/-- The lambda box retains the address after the existing bound-variable cast. -/
def lambdaBoxSite {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {r U V} (s : Site G r U V) : Site (lambdaBox G) r U V :=
  boxSite (s.castHost rfl (by rw [Nat.add_comm k 1]))

noncomputable def lambdaBox_filling {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (lambdaBoxSite s) A) (lambdaBox (plugAt s A)) := by
  have f := box_filling (s.castHost rfl (congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1))) A
  rw [plugAt_castHost] at f
  exact DeepIso.ofIso f

/-- Lift an arbitrary body occurrence through the full abstraction constructor. -/
def abstractionSite {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {r U V} (s : Site G r U V) : Site (abstraction G) r U V :=
  Serial.leftSite (singleUse (d+1) k h)
    (Serial.rightSite (primitiveNet (d+1) (.operation .lam)) (lambdaBoxSite s))

/-- Addressed filling commutes with the entire original abstraction clause. -/
noncomputable def abstraction_filling {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (abstractionSite s) A) (abstraction (plugAt s A)) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr ((Serial.plugAt_right _ _ A).trans
      (Serial.congr (DeepIso.refl _) (lambdaBox_filling s A))) (DeepIso.refl _))

/-- The original abstraction constructor preserves recursive isomorphism. -/
def abstraction_congr {d k h} {G H : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : DeepIso G H) : DeepIso (abstraction G) (abstraction H) :=
  Serial.congr (Serial.congr (DeepIso.refl _) (box_congr (castInterfaces_congr _ _ f))) (DeepIso.refl _)

/-- Lift any nested address through a unary operation without changing its depth. -/
def unarySite {d k h} (o : Unary) {G : Hypernet d [.term] (environmentInterface k h)}
    {r U V} (s : Site G r U V) : Site (unary o G) r U V :=
  Serial.leftSite (singleUse d k h)
    (Serial.rightSite (primitiveNet d (.operation (.unary o))) s)

/-- Unlike the shallow edge law, this law also covers occurrences below boxes. -/
noncomputable def unary_filling {d k h} (o : Unary) {G : Hypernet d [.term] (environmentInterface k h)}
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (unarySite o s) A) (unary o (plugAt s A)) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr (Serial.plugAt_right _ _ A) (DeepIso.refl _))
/-- The abstraction constructor retains the chosen hole's uniqueness. -/
theorem abstractionSite_sole {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    {r U V} (s : Site G r U V) (sole : SoleHole s) : SoleHole (abstractionSite s) :=
  Serial.leftSite_sole _ (language_holeFree (singleUse_language _ _ _)) _
    (Serial.rightSite_sole _ (SingleHole.operation_holeFree _ _) _
      (boxSite_sole _ (SoleHole.castHost _ _ s sole)))

/-- The unary constructor retains the chosen hole's uniqueness at every depth. -/
theorem unarySite_sole {d k h} (o : Unary) {G : Hypernet d [.term] (environmentInterface k h)}
    {r U V} (s : Site G r U V) (sole : SoleHole s) : SoleHole (unarySite o s) :=
  Serial.leftSite_sole _ (language_holeFree (singleUse_language _ _ _)) _
    (Serial.rightSite_sole (primitiveNet d (.operation (.unary o)))
      (SingleHole.operation_holeFree d (.unary o)) s sole)
end Translation
end Hypernets.Copying

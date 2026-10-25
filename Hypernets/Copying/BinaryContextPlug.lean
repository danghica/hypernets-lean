import Hypernets.Copying.ParallelContextPlug

/-! Actual filling through the unmodified pair, application and binary clauses. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph

/-- Carry a left argument address through the prescribed middle-block exchange. -/
def pairLeftSite {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (H : Hypernet d [.term] (environmentInterface k h)) {r U V} (s : Site G r U V) :
    Site (pair G H) r U V :=
  (ParallelPair.leftSite (pairBoundary k h) H s).castHost rfl
    (by simp [environmentInterface,Nat.mul_two])

/-- Carry a right argument address through the same prescribed exchange. -/
def pairRightSite {d k h} (G : Hypernet d [.term] (environmentInterface k h))
    {H : Hypernet d [.term] (environmentInterface k h)} {r U V} (s : Site H r U V) :
    Site (pair G H) r U V :=
  (ParallelPair.rightSite (pairBoundary k h) G s).castHost rfl
    (by simp [environmentInterface,Nat.mul_two])

noncomputable def pairLeft_filling {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (H : Hypernet d [.term] (environmentInterface k h)) {r U V} (s : Site G r U V)
    (A : Hypernet r U V) : DeepIso (plugAt (pairLeftSite H s) A) (pair (plugAt s A) H) := by
  unfold pairLeftSite
  rw [plugAt_castHost]
  exact castInterfaces_congr _ _ (ParallelPair.plugAt_left (pairBoundary k h) H s A)

noncomputable def pairRight_filling {d k h} (G : Hypernet d [.term] (environmentInterface k h))
    {H : Hypernet d [.term] (environmentInterface k h)} {r U V} (s : Site H r U V)
    (A : Hypernet r U V) : DeepIso (plugAt (pairRightSite G s) A) (pair G (plugAt s A)) := by
  unfold pairRightSite
  rw [plugAt_castHost]
  exact castInterfaces_congr _ _ (ParallelPair.plugAt_right (pairBoundary k h) G s A)

/-- The original grouped pair construction preserves recursive isomorphism. -/
def pair_congr {d k h} {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (f : DeepIso G G') (g : DeepIso H H') : DeepIso (pair G H) (pair G' H') :=
  castInterfaces_congr _ _ (ParallelPair.congr (pairBoundary k h) f g)

theorem pairLeftSite_sole {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (H : Hypernet d [.term] (environmentInterface k h)) (free : HoleFree H)
    {r U V} (s : Site G r U V) (sole : SoleHole s) : SoleHole (pairLeftSite H s) :=
  SoleHole.castHost _ _ _ (ParallelPair.leftSite_sole (pairBoundary k h) H free s sole)

theorem pairRightSite_sole {d k h} (G : Hypernet d [.term] (environmentInterface k h))
    {H : Hypernet d [.term] (environmentInterface k h)} (free : HoleFree G)
    {r U V} (s : Site H r U V) (sole : SoleHole s) : SoleHole (pairRightSite G s) :=
  SoleHole.castHost _ _ _ (ParallelPair.rightSite_sole (pairBoundary k h) G free s sole)

/-- Lift a left argument occurrence through the literal application clause. -/
def applicationLeftSite {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site G r U V) : Site (application G H) r U V :=
  Serial.leftSite (environmentDistributor d k h 2)
    (Serial.rightSite (primitiveNet d (.operation .app)) (pairLeftSite H s))

/-- Filling commutes with the full application clause, retaining the distributors. -/
noncomputable def applicationLeft_filling {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (applicationLeftSite H s) A) (application (plugAt s A) H) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr ((Serial.plugAt_right _ _ A).trans
      (Serial.congr (DeepIso.refl _) (pairLeft_filling H s A))) (DeepIso.refl _))

/-- The lifted occurrence is sole when the fixed argument is hole-free. -/
theorem applicationLeftSite_sole {d k h} {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    (free : HoleFree H) {r U V} (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (applicationLeftSite H s) :=
  Serial.leftSite_sole _ (language_holeFree (environmentDistributor_language _ _ _ _)) _
    (Serial.rightSite_sole (primitiveNet d (.operation .app))
      (SingleHole.operation_holeFree d .app) _ (pairLeftSite_sole H free s sole))

/-- Lift a right argument occurrence through the literal application clause. -/
def applicationRightSite {d k h} {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site H r U V) : Site (application G H) r U V :=
  Serial.leftSite (environmentDistributor d k h 2)
    (Serial.rightSite (primitiveNet d (.operation .app)) (pairRightSite G s))

/-- Filling commutes with the full application clause, retaining the distributors. -/
noncomputable def applicationRight_filling {d k h} {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site H r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (applicationRightSite G s) A) (application G (plugAt s A)) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr ((Serial.plugAt_right _ _ A).trans
      (Serial.congr (DeepIso.refl _) (pairRight_filling G s A))) (DeepIso.refl _))

/-- The lifted occurrence is sole when the fixed argument is hole-free. -/
theorem applicationRightSite_sole {d k h} {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    (free : HoleFree G) {r U V} (s : Site H r U V) (sole : SoleHole s) :
    SoleHole (applicationRightSite G s) :=
  Serial.leftSite_sole _ (language_holeFree (environmentDistributor_language _ _ _ _)) _
    (Serial.rightSite_sole (primitiveNet d (.operation .app))
      (SingleHole.operation_holeFree d .app) _ (pairRightSite_sole G free s sole))

/-- Recursive argument isomorphisms preserve the original application graph. -/
def application_congr {d k h} {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (f : DeepIso G G') (g : DeepIso H H') : DeepIso (application G H) (application G' H') :=
  Serial.congr (Serial.congr (DeepIso.refl _) (pair_congr f g)) (DeepIso.refl _)

/-- Lift a left argument occurrence through the literal binary clause. -/
def binaryLeftSite {d k h} (o : Binary) {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site G r U V) : Site (binary o G H) r U V :=
  Serial.leftSite (environmentDistributor d k h 2)
    (Serial.rightSite (primitiveNet d (.operation (.binary o))) (pairLeftSite H s))

/-- Filling commutes with the full binary clause, retaining the distributors. -/
noncomputable def binaryLeft_filling {d k h} (o : Binary) {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (binaryLeftSite o H s) A) (binary o (plugAt s A) H) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr ((Serial.plugAt_right _ _ A).trans
      (Serial.congr (DeepIso.refl _) (pairLeft_filling H s A))) (DeepIso.refl _))

/-- The lifted occurrence is sole when the fixed argument is hole-free. -/
theorem binaryLeftSite_sole {d k h} (o : Binary) {G : Hypernet d [.term] (environmentInterface k h)} (H : Hypernet d [.term] (environmentInterface k h))
    (free : HoleFree H) {r U V} (s : Site G r U V) (sole : SoleHole s) :
    SoleHole (binaryLeftSite o H s) :=
  Serial.leftSite_sole _ (language_holeFree (environmentDistributor_language _ _ _ _)) _
    (Serial.rightSite_sole (primitiveNet d (.operation (.binary o)))
      (SingleHole.operation_holeFree d (.binary o)) _ (pairLeftSite_sole H free s sole))

/-- Lift a right argument occurrence through the literal binary clause. -/
def binaryRightSite {d k h} (o : Binary) {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site H r U V) : Site (binary o G H) r U V :=
  Serial.leftSite (environmentDistributor d k h 2)
    (Serial.rightSite (primitiveNet d (.operation (.binary o))) (pairRightSite G s))

/-- Filling commutes with the full binary clause, retaining the distributors. -/
noncomputable def binaryRight_filling {d k h} (o : Binary) {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    {r U V} (s : Site H r U V) (A : Hypernet r U V) :
    DeepIso (plugAt (binaryRightSite o G s) A) (binary o G (plugAt s A)) :=
  (Serial.plugAt_left _ _ A).trans
    (Serial.congr ((Serial.plugAt_right _ _ A).trans
      (Serial.congr (DeepIso.refl _) (pairRight_filling G s A))) (DeepIso.refl _))

/-- The lifted occurrence is sole when the fixed argument is hole-free. -/
theorem binaryRightSite_sole {d k h} (o : Binary) {H : Hypernet d [.term] (environmentInterface k h)} (G : Hypernet d [.term] (environmentInterface k h))
    (free : HoleFree G) {r U V} (s : Site H r U V) (sole : SoleHole s) :
    SoleHole (binaryRightSite o G s) :=
  Serial.leftSite_sole _ (language_holeFree (environmentDistributor_language _ _ _ _)) _
    (Serial.rightSite_sole (primitiveNet d (.operation (.binary o)))
      (SingleHole.operation_holeFree d (.binary o)) _ (pairRightSite_sole G free s sole))

/-- Recursive argument isomorphisms preserve the original binary graph. -/
def binary_congr {d k h} (o : Binary) {G G' H H' : Hypernet d [.term] (environmentInterface k h)}
    (f : DeepIso G G') (g : DeepIso H H') : DeepIso (binary o G H) (binary o G' H') :=
  Serial.congr (Serial.congr (DeepIso.refl _) (pair_congr f g)) (DeepIso.refl _)

end Hypernets.Copying.Translation

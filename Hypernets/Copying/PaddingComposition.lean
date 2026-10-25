import Hypernets.Copying.PaddingPlug
import Hypernets.Copying.NestedContextFilling

/-! Exact depth transports and additive composition of the original padding. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
namespace Translation

theorem pad_castDepth {d e I O} (eq : d = e) (G : Hypernet d I O) (n : Nat) :
    pad e n (castDepth eq G) = castDepth (congrArg (· + n) eq) (pad d n G) := by
  cases eq; rfl

theorem raise_castDepth {d e I O} (eq : d = e) (G : Hypernet d I O) :
    raise e (castDepth eq G) = castDepth (congrArg (· + 1) eq) (raise d G) := by
  cases eq; rfl

/-- Successive padding adds the two allowances; only equality of depth indices
is transported, with the existing graph constructors retained. -/
theorem pad_add (d n m : Nat) {I O} (G : Hypernet d I O) :
    pad (d+n) m (pad d n G) = castDepth (Nat.add_assoc d n m).symm (pad d (n+m) G) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pad,ih,raise_castDepth]
    rfl

noncomputable def castDepth_congr {d e I O} (eq : d = e) {G H : Hypernet d I O}
    (f : DeepIso G H) : DeepIso (castDepth eq G) (castDepth eq H) := by cases eq; exact f

noncomputable def padTo_congr {d I O} (n : Nat) (bound : d ≤ n) {G H : Hypernet d I O}
    (f : DeepIso G H) : DeepIso (padTo n bound G) (padTo n bound H) :=
  castDepth_congr _ (Padding.pad_congr f _)
end Translation

/-- Transport the host allowance while retaining a site's local allowance. -/
def Site.castDepth {d e I O} {G : Hypernet d I O} (eq : d = e)
    {r U V} (s : Site G r U V) : Site (Translation.castDepth eq G) r U V := by
  cases eq; exact s

theorem plugAt_castDepth {d e I O} {G : Hypernet d I O} (eq : d = e)
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    plugAt (s.castDepth eq) A = Translation.castDepth eq (plugAt s A) := by cases eq; rfl

theorem SoleHole.castDepth {d e I O} {G : Hypernet d I O} (eq : d = e)
    {r U V} (s : Site G r U V) (sole : SoleHole s) : SoleHole (s.castDepth eq) := by
  cases eq; exact sole

/-- Transport the local allowance separately from the host allowance. -/
def Site.castLocal {d I O} {G : Hypernet d I O} {r q U V} (eq : r = q)
    (s : Site G r U V) : Site G q U V := by cases eq; exact s

theorem plugAt_castLocal {d I O} {G : Hypernet d I O} {r q U V} (eq : r = q)
    (s : Site G r U V) (A : Hypernet q U V) :
    plugAt (s.castLocal eq) A = plugAt s (Translation.castDepth eq.symm A) := by cases eq; rfl

theorem SoleHole.castLocal {d I O} {G : Hypernet d I O} {r q U V} (eq : r = q)
    (s : Site G r U V) (sole : SoleHole s) : SoleHole (s.castLocal eq) := by
  cases eq; exact sole
namespace Padding
/-- Add host padding while recording the accumulated padding at the local hole. -/
noncomputable def extendSite {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (m : Nat) :
    Site (Translation.pad h m C) (d+(n+m)) U V :=
  (padSite s m).castLocal (Nat.add_assoc d n m)

theorem extendSite_sole {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (sole : SoleHole s) (m : Nat) : SoleHole (extendSite s m) :=
  SoleHole.castLocal _ _ (padSite_sole s sole m)

noncomputable def extend_filling {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (A : Hypernet d U V) (m : Nat) :
    DeepIso (plugAt (extendSite s m) (Translation.pad d (n+m) A))
      (Translation.pad h m (plugAt s (Translation.pad d n A))) := by
  unfold extendSite
  rw [plugAt_castLocal, ← Translation.pad_add]
  exact (pad_filling s (Translation.pad d n A) m).symm

/-- Lift to a common host allowance, adding only its actual deficit locally. -/
noncomputable def toSite {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (N : Nat) (bound : h ≤ N) :
    Site (Translation.padTo N bound C) (d+(n+(N-h))) U V :=
  (extendSite s (N-h)).castDepth (Nat.add_sub_of_le bound)

theorem toSite_sole {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (sole : SoleHole s) (N : Nat) (bound : h ≤ N) :
    SoleHole (toSite s N bound) := SoleHole.castDepth _ _ (extendSite_sole s sole _)

noncomputable def to_filling {h I O} {C : Hypernet h I O} {d n U V}
    (s : Site C (d+n) U V) (A : Hypernet d U V) (N : Nat) (bound : h ≤ N) :
    DeepIso (plugAt (toSite s N bound) (Translation.pad d (n+(N-h)) A))
      (Translation.padTo N bound (plugAt s (Translation.pad d n A))) := by
  unfold toSite
  rw [plugAt_castDepth]
  exact Translation.castDepth_congr _ (extend_filling s A _)
end Padding
end Hypernets.Copying

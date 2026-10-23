import Hypernets.Graph.DeepContext
import Hypernets.Graph.Examples

/-! Nonvacuous context composition, label reuse, and freshness regressions. -/

namespace Hypernets.Linear.Examples

open Graph

theorem value_holeFree : HoleFree value := by
  rintro h ⟨a, ha⟩
  cases ha

theorem filledBox_unique : UniqueHoles operations 1 filledBox :=
  plugAt_holeFree_unique boxedHoleSite value boxedContext.property value_holeFree

noncomputable def filledContext : Context operations 1 [.thunk 0] [] :=
  boxedContext.plugAt boxedHoleSite ⟨value, holeFree_unique value_holeFree⟩
    (holeFree_disjoint boxedHole value_holeFree)

theorem singleHole_retained_absent (h : Hole) : ¬ RetainedHole singleHole 0 h := by
  rintro ⟨e, ne, _, _⟩
  apply ne
  apply Fin.ext
  omega

/-- Reusing the removed label is allowed by the sharp freshness condition. -/
theorem reuse_removed_label : UniqueHoles operations 0 (singleHole.plug 0 singleHole) :=
  plug_uniqueHoles_of_fresh singleHole 0 singleHole singleHole_unique singleHole_unique
    (fun h retained _ => singleHole_retained_absent h retained)

/-- Full host/replacement disjointness would incorrectly exclude this valid reuse. -/
theorem reuse_not_fully_disjoint : ¬ HolesDisjoint singleHole singleHole :=
  fun fresh => fresh holeLabel ⟨(0 : Fin 1), rfl⟩ ⟨(0 : Fin 1), rfl⟩

theorem filled_single_holeFree : HoleFree (singleHole.plug 0 value) := by
  intro h present
  cases (plug_hasHole_iff singleHole 0 value h).mp present with
  | inl retained => exact singleHole_retained_absent h retained
  | inr inserted => exact value_holeFree h inserted

/-- Hole removal is global: the filled box has no holes at any depth. -/
theorem filledBox_holeFree : HoleFree filledBox := by
  intro h present
  obtain ⟨⟨e, x⟩, hx⟩ := (hasHole_iff_occurrences filledBox h).mp present
  have zero : e = (0 : Fin 1) := by apply Fin.ext; omega
  subst e
  change fiberHole operations 1 (filledBox.edgeLabel (0 : Fin 1)) x = some h at hx
  have absent (y : Fiber operations 1
      (Sum.inr (⟨0, 0, singleHole.plug 0 value⟩ : Box (alphabet operations 0)))) :
      fiberHole operations 1 _ y ≠ some h := by
    cases y with
    | inl u => intro bad; cases bad
    | inr child => exact fun bad => filled_single_holeFree h ⟨child, bad⟩
  exact absent _ ((fiberHole_transport filled_box_body x).trans hx)

/-- Two different hole labels with the same one-term input/output type. -/
def chainHole (name : Nat) : Hole := ⟨name, [.term], [.term]⟩

/-- Two consecutive shallow holes, with one shared internal vertex. -/
@[reducible] def twoHoles : Hypernet operations 0 [.term] [.term] where
  Internal := Fin 1
  Edge := Fin 2
  finiteInternal := Enumeration.fin 1
  finiteEdge := Enumeration.fin 2
  internalLabel _ := .term
  edgeLabel e := ⟨.hole (chainHole (if e = 0 then 0 else 1))⟩
  source e := if e = 0 then [.input 0] else [.internal 0]
  target e := if e = 0 then [.internal 0] else [.output 0]
  source_nodup e := by split <;> simp
  target_nodup e := by split <;> simp
  source_unique := by
    intro v e f he hf
    by_cases h : e = 0 <;> by_cases k : f = 0 <;> simp_all
    apply Fin.ext
    have := e.isLt
    have := f.isLt
    omega
  target_unique := by
    intro v e f he hf
    by_cases h : e = 0 <;> by_cases k : f = 0 <;> simp_all
    apply Fin.ext
    have := e.isLt
    have := f.isLt
    omega
  source_coverage := by
    intro v
    cases v with
    | internal i =>
        have hi : i = 0 := by
          apply Fin.ext
          change i.val = 0
          have h : i.val < 1 := i.isLt
          omega
        subst i
        exact ⟨fun _ => by simp [Port.IsOutput], fun _ => ⟨1, by simp⟩⟩
    | input i =>
        have hi : i = 0 := by
          apply Fin.ext
          change i.val = 0
          have h : i.val < 1 := i.isLt
          omega
        subst i
        exact ⟨fun _ => by simp [Port.IsOutput], fun _ => ⟨0, by simp⟩⟩
    | output i =>
        simp [Port.IsOutput]
  target_coverage := by
    intro v
    cases v with
    | internal i =>
        have hi : i = 0 := by
          apply Fin.ext
          change i.val = 0
          have h : i.val < 1 := i.isLt
          omega
        subst i
        exact ⟨fun _ => by simp [Port.IsInput], fun _ => ⟨0, by simp⟩⟩
    | output i =>
        have hi : i = 0 := by
          apply Fin.ext
          change i.val = 0
          have h : i.val < 1 := i.isLt
          omega
        subst i
        exact ⟨fun _ => by simp [Port.IsInput], fun _ => ⟨1, by simp⟩⟩
    | input i => simp [Port.IsInput]
  source_typed e := by split <;> simp [Port.label, alphabet, baseAlphabet, primitiveSignature, chainHole]
  target_typed e := by split <;> simp [Port.label, alphabet, baseAlphabet, primitiveSignature, chainHole]

theorem twoHoles_unique : UniqueHoles operations 0 twoHoles := by
  intro h a b ha hb
  change Fin 2 at a b
  have labels : chainHole (if a = 0 then 0 else 1) = chainHole (if b = 0 then 0 else 1) :=
    (Option.some.inj ha).trans (Option.some.inj hb).symm
  have names := congrArg Hole.name labels
  change (if a = 0 then 0 else 1) = (if b = 0 then 0 else 1) at names
  clear labels ha hb h
  by_cases za : a = 0
  · by_cases zb : b = 0
    · exact za.trans zb.symm
    · simp [za, zb] at names
  · by_cases zb : b = 0
    · simp [za, zb] at names
    · apply Fin.ext
      have an : a.val ≠ 0 := fun eq => za (Fin.ext eq)
      have bn : b.val ≠ 0 := fun eq => zb (Fin.ext eq)
      have := a.isLt
      have := b.isLt
      omega

@[reducible] def repeatedHole : Hypernet operations 0 [.term] [.term] :=
  Net.corolla (baseAlphabet operations).signature ⟨.hole (chainHole 1)⟩

theorem repeatedHole_unique : UniqueHoles operations 0 repeatedHole := by
  intro _ a b _ _
  apply Fin.ext
  have := a.isLt
  have := b.isLt
  omega

/-- Two valid input contexts can compose to an invalid context without freshness. -/
theorem collision_breaks_unique : ¬ UniqueHoles operations 0 (twoHoles.plug 0 repeatedHole) := by
  intro unique
  have eq := unique (chainHole 1)
    (Sum.inl (⟨(1 : Fin 2), by decide⟩ : {e : Fin 2 // e ≠ 0}))
    (Sum.inr (0 : Fin 1)) rfl rfl
  cases eq

theorem collision_not_fresh : ¬ PlugFresh twoHoles 0 repeatedHole := by
  intro fresh
  exact fresh (chainHole 1)
    ⟨1, by decide, .inl (), rfl⟩ ⟨(0 : Fin 1), rfl⟩

end Hypernets.Linear.Examples

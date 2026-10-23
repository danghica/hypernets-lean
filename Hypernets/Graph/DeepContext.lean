import Hypernets.Graph.ContextPlugging

/-! Compositional provenance and context closure for replacement at any depth. -/

namespace Hypernets.Linear

open Graph

variable {Op : Type} {ops : Operations Op}

/-- Local provenance for changing one edge label, possibly changing a box body. -/
structure FiberProvenance {d r J K} (old new : (alphabet ops d).Symbol)
    (H : Hypernet ops r J K) where
  origin : Fiber ops d new → Fiber ops d old ⊕ Occurrences H
  injective : ∀ {a b}, origin a = origin b → a = b
  hole : ∀ a, fiberHole ops d new a =
    match origin a with
    | .inl old => fiberHole ops d _ old
    | .inr new => occurrenceHole H new

/-- A label that is unchanged has entirely retained provenance. -/
def FiberProvenance.unchanged {d r J K} (label : (alphabet ops d).Symbol)
    (H : Hypernet ops r J K) : FiberProvenance label label H where
  origin := Sum.inl
  injective := Sum.inl.inj
  hole _ := rfl

/-- Retain a fibre whose label agrees propositionally with its former label. -/
def FiberProvenance.retained {d r J K} {old new : (alphabet ops d).Symbol}
    (eq : new = old) (H : Hypernet ops r J K) : FiberProvenance old new H where
  origin x := .inl (eq ▸ x)
  injective h := fiber_transport_injective eq (Sum.inl.inj h)
  hole x := (fiberHole_transport eq x).symm

/-- Assemble local fibre provenance; only one edge may produce inserted origins. -/
def relabelProvenance {d r I O J K} (G : Hypernet ops d I O) (selected : G.Edge)
    (labels : G.Edge → (alphabet ops d).Symbol)
    (input : ∀ e, (alphabet ops d).signature.input (labels e) =
      (alphabet ops d).signature.input (G.edgeLabel e))
    (output : ∀ e, (alphabet ops d).signature.output (labels e) =
      (alphabet ops d).signature.output (G.edgeLabel e))
    (H : Hypernet ops r J K)
    (pieces : ∀ e, FiberProvenance (G.edgeLabel e) (labels e) H)
    (only : ∀ e, e ≠ selected → ∀ x, ∃ y, (pieces e).origin x = .inl y) :
    Provenance (G.relabelEdges _ labels input output) G H where
  origin a := match (pieces a.1).origin a.2 with
    | .inl old => .inl ⟨a.1, old⟩
    | .inr new => .inr new
  injective := by
    classical
    rintro ⟨e, x⟩ ⟨f, y⟩ eq
    cases ex : (pieces e).origin x with
    | inl old =>
        cases ey : (pieces f).origin y with
        | inl old' =>
            simp only [ex, ey] at eq
            have pair := Sum.inl.inj eq
            have ef : e = f := congrArg Sigma.fst pair
            subst f
            have oo : old = old' := eq_of_heq (Sigma.mk.inj pair).2
            have xy := (pieces e).injective (ex.trans ((congrArg Sum.inl oo).trans ey.symm))
            subst y
            rfl
        | inr new => simp [ex, ey] at eq
    | inr new =>
        cases ey : (pieces f).origin y with
        | inl old => simp [ex, ey] at eq
        | inr new' =>
            have es : e = selected := by
              by_cases ne : e = selected
              · exact ne
              obtain ⟨old, he⟩ := only e ne x
              rw [ex] at he
              cases he
            have fs : f = selected := by
              by_cases ne : f = selected
              · exact ne
              obtain ⟨old, he⟩ := only f ne y
              rw [ey] at he
              cases he
            have ef : e = f := es.trans fs.symm
            clear es fs
            subst f
            simp only [ex, ey] at eq
            have nn := Sum.inr.inj eq
            have xy := (pieces e).injective (ex.trans ((congrArg Sum.inr nn).trans ey.symm))
            subst y
            rfl
  hole a := by
    have h := (pieces a.1).hole a.2
    cases eq : (pieces a.1).origin a.2 <;> simpa [occurrenceHole, eq] using h

/-- A changed box retains its own shallow occurrence, and lifts the provenance
of body occurrences without altering their identities. -/
def boxFiberProvenance {d r bound free J K}
    (old new : Hypernet ops d [.term] (List.replicate (bound + free) .term))
    (H : Hypernet ops r J K) (p : Provenance new old H) :
    FiberProvenance (d := d + 1)
      (Sum.inr (⟨bound, free, old⟩ : Box (alphabet ops d)))
      (Sum.inr (⟨bound, free, new⟩ : Box (alphabet ops d))) H where
  origin
    | .inl u => .inl (.inl u)
    | .inr child => match p.origin ((occurrenceBijection ops d new).toFun child) with
      | .inl retained => .inl (.inr ((occurrenceBijection ops d old).invFun retained))
      | .inr inserted => .inr inserted
  injective := by
    intro a b eq
    cases a with
    | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj eq))
        | inr b =>
            cases h : p.origin ((occurrenceBijection ops d new).toFun b) <;> simp [h] at eq
    | inr a =>
        cases b with
        | inl b =>
            cases h : p.origin ((occurrenceBijection ops d new).toFun a) <;> simp [h] at eq
        | inr b =>
            have orig : p.origin ((occurrenceBijection ops d new).toFun a) =
                p.origin ((occurrenceBijection ops d new).toFun b) := by
              cases ha : p.origin ((occurrenceBijection ops d new).toFun a) with
              | inl a' =>
                  cases hb : p.origin ((occurrenceBijection ops d new).toFun b) with
                  | inl b' =>
                      simp only [ha, hb] at eq
                      have child := Sum.inr.inj (Sum.inl.inj eq)
                      have pair := congrArg (occurrenceBijection ops d old).toFun child
                      have pair' : a' = b' := by simpa [(occurrenceBijection ops d old).right_inv] using pair
                      exact congrArg Sum.inl pair'
                  | inr b' => simp [ha, hb] at eq
              | inr a' =>
                  cases hb : p.origin ((occurrenceBijection ops d new).toFun b) with
                  | inl b' => simp [ha, hb] at eq
                  | inr b' => simpa [ha, hb] using eq
            exact congrArg Sum.inr ((occurrenceBijection ops d new).injective (p.injective orig))
  hole a := by
    cases a with
    | inl a => rfl
    | inr a =>
        have h := p.hole ((occurrenceBijection ops d new).toFun a)
        rw [occurrenceBijection_hole (ops := ops) d new a] at h
        cases eq : p.origin ((occurrenceBijection ops d new).toFun a) with
        | inl old' =>
            have preserved := occurrenceBijection_hole d old ((occurrenceBijection ops d old).invFun old')
            rw [(occurrenceBijection ops d old).right_inv] at preserved
            simpa [fiberHole, childHole, eq, preserved] using h
        | inr new' => simpa [fiberHole, childHole, eq] using h

/-- Lift body provenance through one selected outer box. -/
noncomputable def replaceBoxProvenance {d r I O J K}
    (G : Hypernet ops (d + 1) I O) (e : G.Edge) (b : Box (alphabet ops d))
    (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops d [.term] (List.replicate (b.bound + b.free) .term))
    (H : Hypernet ops r J K) (p : Provenance body b.body H) :
    Provenance (replaceBox G e b label body) G H := by
  classical
  let labels : G.Edge → (alphabet ops (d + 1)).Symbol := fun f =>
    if f = e then .inr ⟨b.bound, b.free, body⟩ else G.edgeLabel f
  let pieces : ∀ f, FiberProvenance (G.edgeLabel f) (labels f) H := by
    intro f
    by_cases h : f = e
    · subst f
      simp only [labels, ↓reduceIte]
      rw [label]
      exact boxFiberProvenance b.body body H p
    · exact FiberProvenance.retained (by simp [labels, h]) H
  refine relabelProvenance G e labels _ _ H pieces ?_
  intro f ne x
  simp only [pieces, dite_eq_right ne]
  exact ⟨_, rfl⟩

/-- Injective, lookup-preserving provenance for replacement at any addressed depth. -/
noncomputable def siteProvenance {Op : Type} {ops : Operations Op}
    {depth : Nat} {I O : List Wire} {G : Hypernet ops depth I O} {r : Nat} {J K : List Wire}
    (site : Site ops G r J K) (H : Hypernet ops r J K) :
    Provenance (plugAt site H) G H := by
  induction site with
  | shallow C e => exact shallowProvenance C e H
  | inside e b label inner ih =>
      exact replaceBoxProvenance _ e b label (plugAt inner H) H (ih H)

/-- The precise provenance-based freshness premise excludes discarded occurrences. -/
theorem plugAt_uniqueHoles_of_compatible {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (ug : UniqueHoles ops depth G) (uh : UniqueHoles ops r H)
    (fresh : (siteProvenance site H).Compatible) :
    UniqueHoles ops depth (plugAt site H) :=
  (siteProvenance site H).unique_of_compatible ug uh fresh

theorem plugAt_uniqueHoles {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (ug : UniqueHoles ops depth G) (uh : UniqueHoles ops r H) (fresh : HolesDisjoint G H) :
    UniqueHoles ops depth (plugAt site H) :=
  (siteProvenance site H).unique ug uh fresh

/-- No hole label is manufactured by replacement, even when crossing box boundaries. -/
theorem plugAt_hasHole_subset {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K) {h}
    (present : HasHole (plugAt site H) h) : HasHole G h ∨ HasHole H h :=
  (siteProvenance site H).holes_subset present

/-- Hole-free material can replace any edge of a context at any depth. -/
theorem plugAt_holeFree_unique {depth I O} {G : Hypernet ops depth I O} {r J K}
    (site : Site ops G r J K) (H : Hypernet ops r J K)
    (ug : UniqueHoles ops depth G) (free : HoleFree H) :
    UniqueHoles ops depth (plugAt site H) :=
  plugAt_uniqueHoles site H ug (holeFree_unique free) (holeFree_disjoint G free)

noncomputable def Context.plugAt {depth I O} (C : Context ops depth I O) {r J K}
    (site : Site ops C.val r J K) (H : Context ops r J K)
    (fresh : HolesDisjoint C.val H.val) : Context ops depth I O :=
  ⟨Linear.plugAt site H.val, plugAt_uniqueHoles site H.val C.property H.property fresh⟩

end Hypernets.Linear

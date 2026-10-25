import Hypernets.Copying.SingleHole
import Hypernets.Copying.BindingPadding

/-! The exact named-hole inventory survives the literal translation assembly. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SingleHole
open Graph

/-- Transport the unique marked edge and all unmarked labels along a bijection. -/
theorem transport {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (h : Hole) (f : Bijection G.Edge H.Edge)
    (mark : ∀ e, SingleHoleLabel h d (G.edgeLabel e) ↔ SingleHoleLabel h r (H.edgeLabel (f.toFun e)))
    (free : ∀ e, LabelAll (fun p => ∀ q, p ≠ .hole q) d (G.edgeLabel e) ↔
      LabelAll (fun p => ∀ q, p ≠ .hole q) r (H.edgeLabel (f.toFun e))) :
    SingleHole h G ↔ SingleHole h H := by
  constructor
  · rintro ⟨e,he,others⟩
    refine ⟨f.toFun e,(mark e).mp he,?_⟩
    intro x ne
    have neq : f.invFun x ≠ e := by intro eq; apply ne; rw [← f.right_inv x,eq]
    have hx := (free (f.invFun x)).mp (others _ neq)
    simpa [f.right_inv] using hx
  · rintro ⟨e,he,others⟩
    refine ⟨f.invFun e,(mark _).mpr (by simpa [f.right_inv] using he),?_⟩
    intro x ne
    apply (free x).mpr
    apply others
    intro eq
    apply ne
    simpa [f.left_inv] using congrArg f.invFun eq

/-- A unique marked component in an ordered parallel family remains unique. -/
theorem parallel {d : Nat} {A : Type} {I O : A → List Wire}
    (G : ∀ a, Hypernet d (I a) (O a)) {J K}
    (B : Net.Parallel.Boundary I O J K) (finite : Enumeration A)
    (h : Hole) (a : A) (one : SingleHole h (G a))
    (rest : ∀ b, b ≠ a → HoleFree (G b)) : SingleHole h (Net.Parallel.net G B finite) := by
  obtain ⟨e,he,others⟩ := one
  refine ⟨⟨a,e⟩,he,?_⟩
  rintro ⟨b,f⟩ ne
  by_cases eq : b = a
  · subst b
    exact others f (fun eq => ne (congrArg (fun x => Sigma.mk a x) eq))
  · exact rest b eq f

/-- Expansion retains the component label inventories exactly. -/
theorem expand {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (h : Hole) (a : C.Edge) (one : SingleHole h (F a))
    (rest : ∀ b, b ≠ a → HoleFree (F b)) : SingleHole h (C.expand F) := by
  obtain ⟨e,he,others⟩ := one
  refine ⟨⟨a,e⟩,he,?_⟩
  rintro ⟨b,f⟩ ne
  by_cases eq : b = a
  · subst b
    exact others f (fun eq => ne (congrArg (fun x => Sigma.mk a x) eq))
  · exact rest b eq f

theorem serial_left {d I J K} (h : Hole) {G : Hypernet d I J} {H : Hypernet d J K}
    (g : SingleHole h G) (hf : HoleFree H) : SingleHole h (Serial.net G H) := by
  apply expand _ _ h false
  · cases d <;> exact g
  · intro b ne; cases b with
    | false => exact False.elim (ne rfl)
    | true => cases d <;> exact hf

theorem serial_right {d I J K} (h : Hole) {G : Hypernet d I J} {H : Hypernet d J K}
    (gf : HoleFree G) (one : SingleHole h H) : SingleHole h (Serial.net G H) := by
  apply expand _ _ h true
  · cases d <;> exact one
  · intro b ne; cases b with
    | true => exact False.elim (ne rfl)
    | false => cases d <;> exact gf

theorem box {d bound k a} (h : Hole)
    {G : Hypernet d [.term] (environmentInterface (bound+k) a)} (one : SingleHole h G) :
    SingleHole h (Copying.box (bound := bound) (freeVariables := k) (freeAtoms := a) G) := by
  refine ⟨(0 : Fin 1),one,?_⟩
  intro e ne
  exact False.elim (ne (Fin.ext (by omega)))

/-- Padding preserves the hole-free status of an individual outer label. -/
theorem freeLabel_raise (d : Nat) {I O} (G : Hypernet d I O) (e : G.Edge) :
    LabelAll (fun p => ∀ q, p ≠ .hole q) (d+1)
      ((raise d G).edgeLabel ((StoreTrace.paddingEdges d G).toFun e)) ↔
    LabelAll (fun p => ∀ q, p ≠ .hole q) d (G.edgeLabel e) := by
  cases d with
  | zero => rfl
  | succ d =>
    cases eq : G.edgeLabel e with
    | inl p => simp [raise,Net.relabel,StoreTrace.paddingEdges,Bijection.refl,eq,LabelAll]
    | inr b =>
      change LabelAll _ (d+2) (match G.edgeLabel e with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩) ↔ _
      rw [eq]
      exact allLabels_raise_iff _ d b.body

theorem raise_iff (h : Hole) (d : Nat) {I O} (G : Hypernet d I O) :
    SingleHole h (raise d G) ↔ SingleHole h G := by
  induction d generalizing I O with
  | zero =>
    apply (transport h (StoreTrace.paddingEdges 0 G) ?_ ?_).symm
    · intro e
      change G.edgeLabel e = ULift.up (.hole h) ↔ (G.edgeLabel e).down = .hole h
      exact ⟨fun eq => congrArg ULift.down eq,fun eq => ULift.ext eq⟩
    · intro e; exact (freeLabel_raise 0 G e).symm
  | succ d ih =>
    apply (transport h (StoreTrace.paddingEdges (d+1) G) ?_ ?_).symm
    · intro e
      cases eq : G.edgeLabel e with
      | inl p => simp [raise,Net.relabel,StoreTrace.paddingEdges,Bijection.refl,eq,SingleHoleLabel]
      | inr b =>
        change _ ↔ SingleHoleLabel h (d+2) (match G.edgeLabel e with
          | .inl p => .inl p
          | .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩)
        rw [eq]
        exact (ih b.body).symm
    · intro e; exact (freeLabel_raise (d+1) G e).symm

theorem castDepth_iff (h : Hole) {d n I O} (eq : d = n) (G : Hypernet d I O) :
    SingleHole h (Translation.castDepth eq G) ↔ SingleHole h G := by cases eq; rfl

theorem pad_iff (h : Hole) (d n : Nat) {I O} (G : Hypernet d I O) :
    SingleHole h (Translation.pad d n G) ↔ SingleHole h G := by
  induction n with
  | zero => rfl
  | succ n ih => exact (raise_iff _ _ _).trans ih

theorem padTo_iff (h : Hole) {d I O} (n : Nat) (bound : d ≤ n) (G : Hypernet d I O) :
    SingleHole h (Translation.padTo n bound G) ↔ SingleHole h G :=
  (castDepth_iff _ _ _).trans (pad_iff _ _ _ _)
end Hypernets.Copying.SingleHole

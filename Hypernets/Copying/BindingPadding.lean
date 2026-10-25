import Hypernets.Copying.BindingInvariance
import Hypernets.Copying.Translation
import Hypernets.Copying.StoreTrace

/-! Binding-free context tests are independent of unused box allowance. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph

/-- Padding changes neither adjacency nor the names of its endpoints. -/
theorem padding_adjacent (d : Nat) {I O} (G : Hypernet d I O) (a b : G.Edge) :
    (raise d G).Adjacent ((StoreTrace.paddingEdges d G).toFun a)
      ((StoreTrace.paddingEdges d G).toFun b) ↔ G.Adjacent a b := by
  cases d <;> rfl

theorem padding_bindingLabel (d : Nat) {I O} (G : Hypernet d I O) (e : G.Edge) :
    BindingLabel (d+1) ((raise d G).edgeLabel ((StoreTrace.paddingEdges d G).toFun e)) ↔
      BindingLabel d (G.edgeLabel e) := by
  cases d with
  | zero =>
    change BindingLabel 1 (.inl (G.edgeLabel e).down) ↔ _
    cases h : G.edgeLabel e with | up p => cases p <;> rfl
  | succ d => cases h : G.edgeLabel e <;>
      simp [BindingLabel,raise,Net.relabel,StoreTrace.paddingEdges,Bijection.refl,h]

theorem padding_holeLabel (d : Nat) {I O} (G : Hypernet d I O) (e : G.Edge) :
    HoleLabel (d+1) ((raise d G).edgeLabel ((StoreTrace.paddingEdges d G).toFun e)) ↔
      HoleLabel d (G.edgeLabel e) := by
  cases d with
  | zero =>
    change (∃ h, Sum.inl (G.edgeLabel e).down = (Sum.inl (.hole h) : (alphabet 1).Symbol)) ↔
      ∃ h, G.edgeLabel e = ULift.up (.hole h)
    constructor
    · rintro ⟨h,eq⟩; exact ⟨h,ULift.ext (Sum.inl.inj eq)⟩
    · rintro ⟨h,eq⟩; rw [eq]; exact ⟨h,rfl⟩
  | succ d =>
    cases h : G.edgeLabel e with
    | inl p =>
      change HoleLabel (d+2) (match G.edgeLabel e with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩) ↔ _
      rw [h]
      constructor <;> rintro ⟨a,eq⟩ <;> exact ⟨a,congrArg Sum.inl (Sum.inl.inj eq)⟩
    | inr b => simp [HoleLabel,primitiveLabel,raise,Net.relabel,StoreTrace.paddingEdges,Bijection.refl,h]

theorem shallow_raise_iff (d : Nat) {I O} (G : Hypernet d I O) :
    ShallowBindingFree (raise d G) ↔ ShallowBindingFree G := by
  constructor
  · intro free
    apply shallow_of_map (StoreTrace.paddingEdges d G).toFun
      (fun h => (padding_adjacent d G _ _).mpr h)
      (fun e h => (padding_bindingLabel d G e).mpr h) ?_
      (fun e h => (padding_holeLabel d G e).mpr h) free
    intro e src; cases d <;> exact src
  · intro free
    let f := StoreTrace.paddingEdges d G
    apply shallow_of_map f.invFun ?_ ?_ ?_ ?_ free
    · intro a b h
      apply (padding_adjacent d G (f.invFun a) (f.invFun b)).mp
      simpa only [f, (StoreTrace.paddingEdges d G).right_inv] using h
    · intro e h
      apply (padding_bindingLabel d G (f.invFun e)).mp
      simpa only [f, (StoreTrace.paddingEdges d G).right_inv] using h
    · intro e src; cases d <;> exact src
    · intro e h
      apply (padding_holeLabel d G (f.invFun e)).mp
      simpa only [f, (StoreTrace.paddingEdges d G).right_inv] using h

/-- The same shallow condition is checked again in every padded box body. -/
theorem paths_raise_iff (d : Nat) {I O} (G : Hypernet d I O) :
    BindingPaths (d+1) (raise d G) ↔ BindingPaths d G := by
  induction d generalizing I O with
  | zero =>
    constructor
    · intro h; exact (shallow_raise_iff 0 G).mp h.1
    · intro h
      refine ⟨(shallow_raise_iff 0 G).mpr h,?_⟩
      intro e; trivial
  | succ d ih =>
    change (_ ∧ _) ↔ (_ ∧ _)
    apply and_congr (shallow_raise_iff (d+1) G)
    apply forall_congr'
    intro e
    cases label : G.edgeLabel e with
    | inl p => simp [raise,Net.relabel,label]
    | inr b => simpa [raise,Net.relabel,label] using ih b.body

theorem raise_iff (d : Nat) {I O} (G : Hypernet d I O) :
    BindingFree (raise d G) ↔ BindingFree G :=
  and_congr (allLabels_raise_iff _ d G) (paths_raise_iff d G)

theorem castDepth_iff {d n I O} (eq : d = n) (G : Hypernet d I O) :
    BindingFree (Translation.castDepth eq G) ↔ BindingFree G := by cases eq; rfl

theorem pad_iff (d n : Nat) {I O} (G : Hypernet d I O) :
    BindingFree (Translation.pad d n G) ↔ BindingFree G := by
  induction n with
  | zero => rfl
  | succ n ih => exact (raise_iff _ _).trans ih

theorem padTo_iff {d I O} (n : Nat) (bound : d ≤ n) (G : Hypernet d I O) :
    BindingFree (Translation.padTo n bound G) ↔ BindingFree G :=
  (castDepth_iff _ _).trans (pad_iff _ _ _)
end Hypernets.Copying.BindingFree

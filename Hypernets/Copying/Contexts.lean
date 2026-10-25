import Hypernets.Copying.BindingInvariance

/-! Single-hole graph contexts with an exact, recursive hole inventory. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- The selected occurrence is the only hole, including all box descendants.
This is stronger than merely having a hole label at the selected edge. -/
def SoleHole {d I O} {G : Hypernet d I O} {r J K} (s : Site G r J K) : Prop := by
  induction s with
  | shallow C e => exact HoleLabel _ (C.edgeLabel e) ∧
      ∀ f, f ≠ e → LabelAll (fun p => ∀ h, p ≠ .hole h) _ (C.edgeLabel f)
  | @inside d I O G e b label r J K s ih =>
    exact ih ∧ (∀ f, f ≠ e → LabelAll (fun p => ∀ h, p ≠ .hole h) _ (G.edgeLabel f))

namespace SoleHole

/-- Filling the unique hole removes all holes, including those at other depths. -/
theorem fill_holeFree {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) (sole : SoleHole s) (H : Hypernet r J K) (hf : HoleFree H) :
    HoleFree (plugAt s H) := by
  induction s with
  | shallow C e =>
    intro f
    cases f with
    | inl f => exact sole.2 f.val f.property
    | inr f => exact hf f
  | @inside d I O G e b label r J K s ih =>
    intro f
    classical
    change LabelAll (fun p => ∀ h, p ≠ .hole h) (d+1)
      (if f = e then .inr ⟨b.bound,b.freeVariables,b.freeAtoms,plugAt s H⟩
       else G.edgeLabel f)
    by_cases eq : f = e
    · simp only [eq,ite_true]
      exact ih sole.1 H hf
    · simpa [eq] using sole.2 f eq

/-- A nonempty local input interface discharges the source condition; no
extra restriction on the surrounding observation context is required. -/
theorem sourced {d I O} {G : Hypernet d I O} {r J K}
    (s : Site G r J K) (sole : SoleHole s) (input : J ≠ []) :
    BindingFree.SourcedHole s := by
  induction s with
  | shallow C e =>
    refine ⟨sole.1,?_⟩
    have ne : C.source e ≠ [] := by
      intro eq
      have len := C.source_length e
      rw [eq] at len
      have : (alphabet _).signature.input (C.edgeLabel e) = [] := by simpa using len.symm
      exact input this
    cases eq : C.source e with
    | nil => exact False.elim (ne eq)
    | cons v vs => exact ⟨v,by simp⟩
  | inside e b label s ih => exact ih sole.1 input

end SoleHole

/-- A concrete closing observation context, with one designated term hole.
The host may nest that hole arbitrarily deeply. Its remaining graph is
unrestricted apart from binding-freedom and the exact hole inventory. -/
structure ClosingContext (r k h : Nat) where
  depth : Nat
  graph : Hypernet depth [.term] []
  site : Site graph r [.term] (environmentInterface k h)
  sole : SoleHole site
  bindingFree : BindingFree graph

namespace ClosingContext
noncomputable def fill {r k h} (C : ClosingContext r k h)
    (G : Hypernet r [.term] (environmentInterface k h)) : Hypernet C.depth [.term] [] :=
  plugAt C.site G

theorem fill_holeFree {r k h} (C : ClosingContext r k h)
    (G : Hypernet r [.term] (environmentInterface k h)) (hf : HoleFree G) :
    HoleFree (C.fill G) := SoleHole.fill_holeFree C.site C.sole G hf

theorem fill_focusFree {r k h} (C : ClosingContext r k h)
    (G : Hypernet r [.term] (environmentInterface k h)) (ff : FocusFree G) :
    FocusFree (C.fill G) := focusFree_closed C.site G C.bindingFree.1 ff

theorem fill_bindingFree {r k h} (C : ClosingContext r k h)
    (G : Hypernet r [.term] (environmentInterface k h)) (bf : BindingFree G) :
    BindingFree (C.fill G) := BindingFree.plugAt C.site G (SoleHole.sourced C.site C.sole (by decide)) C.bindingFree bf
end ClosingContext
end Hypernets.Copying

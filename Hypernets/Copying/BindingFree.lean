import Hypernets.Copying.Predicates
import Hypernets.Graph.FiniteTrace

/-! Binding-free paths are nonempty paths, not reflexive reachability.
A path stays at one box depth; the condition is checked again inside every box. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- The four kinds of edge excluded upstream of a hole in Definition 11.2. -/
def BindingLabel : (d : Nat) → (alphabet d).Symbol → Prop
  | 0, .up p => match p with
    | .contraction _ | .instanceEdge | .hole _ => True
    | _ => False
  | _+1, .inl p => match p with
    | .contraction _ | .instanceEdge | .hole _ => True
    | _ => False
  | _+1, .inr _ => True

def HoleLabel (d : Nat) (a : (alphabet d).Symbol) : Prop :=
  ∃ h, a = primitiveLabel d (.hole h)

/-- Reflexive edge ancestry. A positive ancestry ending at a hole describes a
nonempty path to a source of that hole, with the hole itself omitted. -/
inductive Ancestor {d I O} (G : Hypernet d I O) : G.Edge → G.Edge → Prop where
  | refl (e) : Ancestor G e e
  | step {e f g} : G.Adjacent e f → Ancestor G f g → Ancestor G e g

def StrictAncestor {d I O} (G : Hypernet d I O) (e f : G.Edge) : Prop :=
  ∃ g, G.Adjacent e g ∧ Ancestor G g f

/-- Literal shallow restriction, including the source witness required by the
paper's phrase "from a source". Zero-input holes have no such witness. -/
def ShallowBindingFree {d I O} (G : Hypernet d I O) : Prop :=
  ∀ e f, BindingLabel d (G.edgeLabel e) → (∃ v, v ∈ G.source e) →
    HoleLabel d (G.edgeLabel f) → ¬ StrictAncestor G e f

/-- Check shallow paths independently in each nested body. -/
def BindingPaths : (d : Nat) → {I O : List Wire} → Hypernet d I O → Prop
  | 0, _, _, G => ShallowBindingFree G
  | n+1, _, _, G => ShallowBindingFree G ∧ ∀ e, match G.edgeLabel e with
    | .inl _ => True
    | .inr b => BindingPaths n b.body

def BindingFree {d I O} (G : Hypernet d I O) : Prop :=
  FocusFree G ∧ BindingPaths d G

namespace Ancestor

theorem trans {d I O} {G : Hypernet d I O} {e f g : G.Edge}
    (p : Ancestor G e f) (q : Ancestor G f g) : Ancestor G e g := by
  induction p with
  | refl => exact q
  | step a _ ih => exact .step a (ih q)

theorem positive_of_ne {d I O} {G : Hypernet d I O} {e f : G.Edge}
    (p : Ancestor G e f) (ne : e ≠ f) : StrictAncestor G e f := by
  cases p with
  | refl => exact False.elim (ne rfl)
  | step a p => exact ⟨_,a,p⟩

theorem map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : G.Edge → H.Edge) (adj : ∀ {a b}, G.Adjacent a b → H.Adjacent (f a) (f b))
    {a b} (p : Ancestor G a b) : Ancestor H (f a) (f b) := by
  induction p with
  | refl => exact .refl _
  | step a _ ih => exact .step (adj a) ih

end Ancestor

namespace BindingFree

theorem hole_binding (d : Nat) {a : (alphabet d).Symbol} (h : HoleLabel d a) :
    BindingLabel d a := by
  obtain ⟨h,rfl⟩ := h
  cases d <;> trivial

/-- A hole cannot be a self-loop in a binding-free graph, even if its type has
no source ports: a self-loop itself supplies a source witness. -/
theorem hole_nonSelfLoop {d I O} {C : Hypernet d I O} (free : ShallowBindingFree C)
    (e : C.Edge) (hole : HoleLabel d (C.edgeLabel e)) :
    Net.Replacement.NonSelfLoop C e := by
  intro v src tgt
  exact free e e (hole_binding d hole) ⟨v,src⟩ hole ⟨e,⟨v,tgt,src⟩,.refl e⟩

theorem shallow_of_holeFree {d I O} (G : Hypernet d I O) (hf : HoleFree G) :
    ShallowBindingFree G := by
  intro e f _ _ hole
  obtain ⟨h,eq⟩ := hole
  have q := hf f
  rw [eq] at q
  cases d <;> exact False.elim (q h rfl)

/-- A globally hole-free graph satisfies the path restriction at every depth. -/
theorem paths_of_holeFree (d : Nat) {I O} (G : Hypernet d I O) (hf : HoleFree G) :
    BindingPaths d G := by
  induction d generalizing I O with
  | zero => exact shallow_of_holeFree G hf
  | succ d ih =>
    refine ⟨shallow_of_holeFree G hf,?_⟩
    intro e
    cases eq : G.edgeLabel e with
    | inl p => trivial
    | inr b =>
      apply ih b.body
      have q := hf e
      rw [eq] at q
      exact q

theorem of_holeFree {d I O} (G : Hypernet d I O) (ff : FocusFree G) (hf : HoleFree G) :
    BindingFree G := ⟨ff,paths_of_holeFree d G hf⟩


/-- Pull the path restriction back along an incidence and label classification map. -/
theorem shallow_of_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : G.Edge → H.Edge)
    (adj : ∀ {a b}, G.Adjacent a b → H.Adjacent (f a) (f b))
    (bad : ∀ e, BindingLabel d (G.edgeLabel e) → BindingLabel r (H.edgeLabel (f e)))
    (src : ∀ e, (∃ v, v ∈ G.source e) → ∃ v, v ∈ H.source (f e))
    (hole : ∀ e, HoleLabel d (G.edgeLabel e) → HoleLabel r (H.edgeLabel (f e)))
    (free : ShallowBindingFree H) : ShallowBindingFree G := by
  intro e g eb es gh path
  obtain ⟨a,ea,p⟩ := path
  exact free (f e) (f g) (bad e eb) (src e es) (hole g gh)
    ⟨f a,adj ea,p.map f adj⟩

end BindingFree
end Hypernets.Copying

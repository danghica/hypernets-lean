import Hypernets.Copying.BindingInvariance
import Hypernets.Copying.BinaryTranslation

/-! Independent components of a parallel translation cannot introduce a
forbidden path into another component, regardless of boundary ordering. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph

variable {d : Nat} {A : Type} {I O : A → List Wire}
    (G : ∀ a, Hypernet d (I a) (O a)) {J K : List Wire}
    (B : Net.Parallel.Boundary I O J K) (finite : Enumeration A)

theorem ancestor_parallel {e f : (Net.Parallel.net G B finite).Edge}
    (p : Ancestor (Net.Parallel.net G B finite) e f) :
    ∃ g : (G e.1).Edge, f = ⟨e.1,g⟩ ∧ Ancestor (G e.1) e.2 g := by
  induction p with
  | refl e => exact ⟨e.2,rfl,.refl _⟩
  | @step e f g adj p ih =>
    obtain ⟨a,e⟩ := e
    obtain ⟨b,f⟩ := f
    have eq := Net.Parallel.adjacent_tag G B finite adj
    subst b
    obtain ⟨z,rfl,q⟩ := ih
    exact ⟨z,rfl,.step ((Net.Parallel.adjacent_same G B finite a e f).mp adj) q⟩

theorem shallow_parallel (free : ∀ a, ShallowBindingFree (G a)) :
    ShallowBindingFree (Net.Parallel.net G B finite) := by
  intro e f bad src hole path
  obtain ⟨a,e⟩ := e
  obtain ⟨g,adj,p⟩ := path
  obtain ⟨b,g⟩ := g
  have eq := Net.Parallel.adjacent_tag G B finite adj
  subst b
  obtain ⟨z,rfl,q⟩ := ancestor_parallel G B finite p
  obtain ⟨v,hv⟩ := src
  obtain ⟨w,hw,_⟩ := List.mem_map.mp hv
  exact free a e z bad ⟨w,hw⟩ hole
    ⟨g,(Net.Parallel.adjacent_same G B finite a e g).mp adj,q⟩

theorem paths_parallel (free : ∀ a, BindingPaths d (G a)) :
    BindingPaths d (Net.Parallel.net G B finite) := by
  cases d with
  | zero => exact shallow_parallel G B finite free
  | succ d =>
    refine ⟨shallow_parallel G B finite (fun a => (free a).1),?_⟩
    intro e
    exact (free e.1).2 e.2

theorem parallel (free : ∀ a, BindingFree (G a)) :
    BindingFree (Net.Parallel.net G B finite) := by
  refine ⟨?_,paths_parallel G B finite (fun a => (free a).2)⟩
  intro e
  exact (free e.1).1 e.2

/-- Interface casts preserve the exact path and recursive-box predicates. -/
theorem castInterfaces_iff {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet d I O) :
    BindingFree (Translation.castInterfaces hi ho G) ↔ BindingFree G := by
  cases hi; cases ho; rfl

/-- The middle-block exchange of Figure 16 changes only boundary order. -/
theorem pair {d k h} {G H : Hypernet d [.term] (environmentInterface k h)}
    (gf : BindingFree G) (hf : BindingFree H) : BindingFree (Translation.pair G H) := by
  apply (castInterfaces_iff _ _ _).mpr
  apply parallel
  intro b
  cases b <;> assumption
end Hypernets.Copying.BindingFree

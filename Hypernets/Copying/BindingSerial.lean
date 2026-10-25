import Hypernets.Copying.BindingInvariance
import Hypernets.Copying.Serial
import Hypernets.Graph.ExpansionAdjacency

/-! Directed serial composition: a path can cross from left to right, never
back. This accounts for operation prefixes and trailing sharing distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph
variable {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)

theorem serial_nonSelfLoop (b : Bool) : Net.Replacement.NonSelfLoop (Serial.pattern d I J K) b := by
  intro v src tgt
  cases b <;>
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp src <;>
    obtain ⟨j,_,eq⟩ := List.mem_map.mp tgt <;> cases eq

theorem serial_no_backward (a : (Serial.filling G H true).Edge)
    (b : (Serial.filling G H false).Edge) :
    ¬ (Serial.net G H).Adjacent ⟨true,a⟩ ⟨false,b⟩ := by
  intro adj
  have cross := Net.Expansion.adjacent_cross (Serial.pattern d I J K) (Serial.filling G H)
    (by decide : true ≠ false) a b adj
  obtain ⟨v,hv,hw⟩ := cross
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv
  obtain ⟨j,_,eq⟩ := List.mem_map.mp hw
  cases eq

theorem serial_ancestor_monotone {e f : (Serial.net G H).Edge}
    (p : Ancestor (Serial.net G H) e f) : e.1 = true → f.1 = true := by
  induction p with
  | refl => exact id
  | @step e g f adj p ih =>
    intro et
    apply ih
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    cases eb <;> cases gb <;> simp_all
    exact False.elim (serial_no_backward G H e g adj)

/-- If both ends of a path have the same side, every edge stays on that side. -/
theorem serial_ancestor_same {e f : (Serial.net G H).Edge}
    (p : Ancestor (Serial.net G H) e f) (same : e.1 = f.1) :
    ∃ g : (Serial.filling G H e.1).Edge, f = ⟨e.1,g⟩ ∧
      Ancestor (Serial.filling G H e.1) e.2 g := by
  induction p with
  | refl e => exact ⟨e.2,rfl,.refl _⟩
  | @step e g f adj p ih =>
    have mid : e.1 = g.1 := by
      obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
      cases eb <;> cases gb
      · rfl
      · have q := serial_ancestor_monotone G H p rfl
        simp_all
      · exact False.elim (serial_no_backward G H e g adj)
      · rfl
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    change eb = gb at mid
    subst gb
    obtain ⟨z,rfl,q⟩ := ih same
    exact ⟨z,rfl,.step ((Net.Expansion.adjacent_same_iff
      (Serial.pattern d I J K) (Serial.filling G H) eb (serial_nonSelfLoop eb) e g).mp adj) q⟩

/-- The only extra case in serial closure is a bad left edge reaching a right
hole. Either an operation-only prefix or a hole-free suffix excludes it. -/
theorem shallow_serial
    (free : ∀ b, ShallowBindingFree (Serial.filling G H b))
    (crossSafe : (∀ e, ¬ BindingLabel d ((Serial.filling G H false).edgeLabel e)) ∨
      (∀ e, ¬ HoleLabel d ((Serial.filling G H true).edgeLabel e))) :
    ShallowBindingFree (Serial.net G H) := by
  intro e f bad src hole path
  obtain ⟨g,adj,p⟩ := path
  have same : e.1 = f.1 := by
    have whole : Ancestor (Serial.net G H) e f := .step adj p
    obtain ⟨eb,e⟩ := e; obtain ⟨fb,f⟩ := f
    cases eb <;> cases fb
    · rfl
    · rcases crossSafe with left | right
      · exact False.elim (left e bad)
      · exact False.elim (right f hole)
    · have q := serial_ancestor_monotone G H whole rfl
      cases q
    · rfl
  have mid : e.1 = g.1 := by
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    cases eb <;> cases gb
    · rfl
    · have q := serial_ancestor_monotone G H p rfl
      simp_all
    · exact False.elim (serial_no_backward G H e g adj)
    · rfl
  obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
  change eb = gb at mid; subst gb
  obtain ⟨z,rfl,q⟩ := serial_ancestor_same G H p same
  obtain ⟨v,hv⟩ := src
  obtain ⟨w,hw,_⟩ := List.mem_map.mp hv
  exact free eb e z bad ⟨w,hw⟩ hole
    ⟨g,(Net.Expansion.adjacent_same_iff (Serial.pattern d I J K) (Serial.filling G H)
      eb (serial_nonSelfLoop eb) e g).mp adj,q⟩


/-- Lift serial closure to all box depths; inner labels retain their bodies. -/
theorem paths_serial
    (free : ∀ b, BindingPaths d (Serial.filling G H b))
    (crossSafe : (∀ e, ¬ BindingLabel d ((Serial.filling G H false).edgeLabel e)) ∨
      (∀ e, ¬ HoleLabel d ((Serial.filling G H true).edgeLabel e))) :
    BindingPaths d (Serial.net G H) := by
  cases d with
  | zero => exact shallow_serial G H free crossSafe
  | succ d =>
    refine ⟨shallow_serial G H (fun b => (free b).1) crossSafe,?_⟩
    intro e
    exact (free e.1).2 e.2

theorem serial (gf : BindingFree G) (hf : BindingFree H)
    (crossSafe : (∀ e, ¬ BindingLabel d (G.edgeLabel e)) ∨
      (∀ e, ¬ HoleLabel d (H.edgeLabel e))) : BindingFree (Serial.net G H) := by
  refine ⟨Serial.focusFree_net gf.1 hf.1,?_⟩
  apply paths_serial G H
  · intro b; cases d <;> cases b <;> first | exact gf.2 | exact hf.2
  · cases d <;> exact crossSafe

/-- A hole-free trailing distributor cannot create a path into an earlier hole. -/
theorem serial_suffix (gf : BindingFree G) (ff : FocusFree H) (hf : HoleFree H) :
    BindingFree (Serial.net G H) := by
  apply serial G H gf (of_holeFree H ff hf)
  right
  intro e hole
  obtain ⟨a,eq⟩ := hole
  have q := hf e
  rw [eq] at q
  cases d <;> exact q a rfl

end Hypernets.Copying.BindingFree

import Hypernets.Copying.BindingSerial
import Hypernets.Copying.ApplicationSafety

/-! Opening connects a body's bound output to a closed argument. Paths may
leave the body for that argument, but cannot return to a hole in the body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BindingFree
open Graph Application
variable {d F O} (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O)

/-- Neither slot of the literal bound-output splice has a self-loop. -/
theorem splice_nonSelfLoop (b : Bool) :
    Net.Replacement.NonSelfLoop (splicePattern d F O) b := by
  intro v src tgt
  cases b
  · change v ∈ [.input 0] at src
    have eq := List.mem_singleton.mp src
    subst v
    change Port.input 0 ∈ Port.internal (0 : Fin 1) :: freePorts F O at tgt
    simp [freePort] at tgt
  · change v ∈ [.internal (0 : Fin 1)] at src
    have eq := List.mem_singleton.mp src
    subst v
    change Port.internal (0 : Fin 1) ∈ valuePorts F O at tgt
    simp [valuePort] at tgt

/-- The closed argument cannot have an edge pointing back into the body. -/
theorem splice_no_backward (a : (spliceFilling B G true).Edge)
    (b : (spliceFilling B G false).Edge) :
    ¬ (splice B G).Adjacent ⟨true,a⟩ ⟨false,b⟩ := by
  intro adj
  obtain ⟨v,tgt,src⟩ := Net.Expansion.adjacent_cross (splicePattern d F O)
    (spliceFilling B G) (by decide : true ≠ false) a b adj
  change v ∈ [.input 0] at src
  have eq := List.mem_singleton.mp src
  subst v
  change Port.input 0 ∈ valuePorts F O at tgt
  simp [valuePort] at tgt

/-- Once an edge path reaches the argument, it stays there. -/
theorem splice_ancestor_monotone {e f : (splice B G).Edge}
    (p : Ancestor (splice B G) e f) : e.1 = true → f.1 = true := by
  induction p with
  | refl => exact id
  | @step e g f adj p ih =>
    intro et
    apply ih
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    cases eb <;> cases gb <;> simp_all
    exact False.elim (splice_no_backward B G e g adj)

/-- A path with both endpoints in one component remains entirely in it. -/
theorem splice_ancestor_same {e f : (splice B G).Edge}
    (p : Ancestor (splice B G) e f) (same : e.1 = f.1) :
    ∃ g : (spliceFilling B G e.1).Edge, f = ⟨e.1,g⟩ ∧
      Ancestor (spliceFilling B G e.1) e.2 g := by
  induction p with
  | refl e => exact ⟨e.2,rfl,.refl _⟩
  | @step e g f adj p ih =>
    have mid : e.1 = g.1 := by
      obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
      cases eb <;> cases gb
      · rfl
      · have q := splice_ancestor_monotone B G p rfl
        simp_all
      · exact False.elim (splice_no_backward B G e g adj)
      · rfl
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    change eb = gb at mid
    subst gb
    obtain ⟨z,rfl,q⟩ := ih same
    exact ⟨z,rfl,.step ((Net.Expansion.adjacent_same_iff (splicePattern d F O)
      (spliceFilling B G) eb (splice_nonSelfLoop eb) e g).mp adj) q⟩

/-- Every potential forbidden path stays in the body when the argument is closed. -/
theorem shallow_splice_suffix
    (free : ∀ b, ShallowBindingFree (spliceFilling B G b))
    (closed : ∀ e, ¬ HoleLabel d ((spliceFilling B G true).edgeLabel e)) :
    ShallowBindingFree (splice B G) := by
  intro e f bad src hole path
  obtain ⟨g,adj,p⟩ := path
  have same : e.1 = f.1 := by
    have whole : Ancestor (splice B G) e f := .step adj p
    obtain ⟨eb,e⟩ := e; obtain ⟨fb,f⟩ := f
    cases eb <;> cases fb
    · rfl
    · exact False.elim (closed f hole)
    · have q := splice_ancestor_monotone B G whole rfl
      cases q
    · rfl
  have mid : e.1 = g.1 := by
    obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
    cases eb <;> cases gb
    · rfl
    · have q := splice_ancestor_monotone B G p rfl
      simp_all
    · exact False.elim (splice_no_backward B G e g adj)
    · rfl
  obtain ⟨eb,e⟩ := e; obtain ⟨gb,g⟩ := g
  change eb = gb at mid
  subst gb
  obtain ⟨z,rfl,q⟩ := splice_ancestor_same B G p same
  obtain ⟨v,hv⟩ := src
  obtain ⟨w,hw,_⟩ := List.mem_map.mp hv
  exact free eb e z bad ⟨w,hw⟩ hole
    ⟨g,(Net.Expansion.adjacent_same_iff (splicePattern d F O)
      (spliceFilling B G) eb (splice_nonSelfLoop eb) e g).mp adj,q⟩

/-- The actual splice preserves binding freedom of the open body when its
argument has no holes. This makes no rootedness or stability assumption. -/
theorem splice_suffix (body : BindingFree B) (argFree : FocusFree G)
    (argClosed : HoleFree G) : BindingFree (splice B G) := by
  have arg := of_holeFree G argFree argClosed
  have components (b) : BindingFree (spliceFilling B G b) := by
    cases d <;> cases b <;> first | exact body | exact arg
  have shallowClosed : ∀ e, ¬ HoleLabel d ((spliceFilling B G true).edgeLabel e) := by
    intro e ⟨h,label⟩
    have hc : HoleFree (spliceFilling B G true) := by cases d <;> exact argClosed
    have bad := hc e
    rw [label] at bad
    cases d <;> exact bad h rfl
  refine ⟨fun e => (components e.1).1 e.2,?_⟩
  cases d with
  | zero => exact shallow_splice_suffix B G (fun b => (components b).2) shallowClosed
  | succ d =>
    refine ⟨shallow_splice_suffix B G (fun b => (components b).2.1) shallowClosed,?_⟩
    intro e
    exact (components e.1).2.2 e.2

end Hypernets.Copying.BindingFree

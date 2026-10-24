import Hypernets.Graph.SearchHistory

/-! Lemma 24 for actual states and recursive state classes. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op} {d : Nat} {kind : Op → OperationKind}
namespace TypedPosition
variable {G : Hypernet ops d [.term] []}

/-- Reset only the mode of a coordinate, retaining its vertex and typing. -/
def restart (p : TypedPosition G) : TypedPosition G := ⟨(.search,p.val.2),p.property⟩

/-- Coordinate search also characterizes recursively renamed state successors. -/
theorem deepSearch_realize_iff (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G)
    (t : State ops d) :
    State.DeepSearch kind (p.realize fg hg) t ↔
      ∃ q : TypedPosition G, SearchStep G kind p.val q.val ∧
        Nonempty (Focussed.DeepIso (q.realize fg hg).focussed t.focussed) := by
  rw [State.deepSearch_iff]
  constructor
  · rintro ⟨u,step,⟨iso⟩⟩
    obtain ⟨q,h,⟨qu⟩⟩ := (p.search_realize_iff fg hg kind u).mp step
    exact ⟨q,h,⟨(Focussed.DeepIso.ofIso qu).trans iso⟩⟩
  · rintro ⟨q,h,iso⟩
    exact ⟨q.realize fg hg,p.search_realize q fg hg h,iso⟩

/-- A successor class has an actual coordinate on the same underlying graph. -/
theorem class_search_iff (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G)
    (t : DeepStateClass ops d) :
    DeepStateClass.Search kind (DeepStateClass.ofState (p.realize fg hg)) t ↔
      ∃ q : TypedPosition G, SearchStep G kind p.val q.val ∧
        DeepStateClass.ofState (q.realize fg hg) = t := by
  induction t using Quotient.inductionOn with
  | h t =>
      change State.DeepSearch kind (p.realize fg hg) t ↔ _
      rw [p.deepSearch_realize_iff fg hg t]
      constructor
      · rintro ⟨q,h,iso⟩; exact ⟨q,h,Quotient.sound iso⟩
      · rintro ⟨q,h,eq⟩; exact ⟨q,h,Quotient.exact eq⟩

/-- Every exact-length class execution lifts to coordinates on its original graph. -/
theorem class_steps_lift (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G)
    {n} {t : DeepStateClass ops d}
    (run : (DeepStateClass.searchMachine kind).Steps n (DeepStateClass.ofState (p.realize fg hg)) t) :
    ∃ q : TypedPosition G, (coordinateMachine G kind).Steps n p.val q.val ∧
      DeepStateClass.ofState (q.realize fg hg) = t := by
  induction n generalizing p t with
  | zero => exact ⟨p,.zero _,run.zero_eq⟩
  | succ n ih =>
      cases run with
      | cons first tail =>
          obtain ⟨q,step,eq⟩ := (p.class_search_iff fg hg _).mp first
          rw [← eq] at tail
          obtain ⟨r,rest,eq'⟩ := ih q tail
          exact ⟨r,.cons step rest,eq'⟩
end TypedPosition

namespace State
/-- The same underlying state with search resumed at the current focus position. -/
noncomputable def restart (s : State ops d) : State ops d :=
  (coordinate s).restart.realize s.focussed.underlying_focusFree
    (s.focussed.underlying_holeFree s.hole_free)

/-- Resetting the focus mode respects recursive state isomorphism. -/
noncomputable def restart_iso {s t : State ops d} (a : Focussed.DeepIso s.focussed t.focussed) :
    Focussed.DeepIso (restart s).focussed (restart t).focussed := by
  have eq : (coordinate s).restart.deepRename a.erased = (coordinate t).restart := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg (fun p => p.val.2) (coordinate_deepIso a)
  have iso := (coordinate s).restart.realize_deepRename a.erased
    s.focussed.underlying_focusFree (s.focussed.underlying_holeFree s.hole_free)
    t.focussed.underlying_focusFree (t.focussed.underlying_holeFree t.hole_free)
  rw [eq] at iso
  exact iso
end State
namespace DeepStateClass
/-- Search restart is well-defined on state classes. -/
noncomputable def restart (s : DeepStateClass ops d) : DeepStateClass ops d :=
  Quotient.liftOn s (fun s => ofState (State.restart s))
    (fun _ _ ⟨a⟩ => Quotient.sound ⟨State.restart_iso a⟩)
end DeepStateClass
namespace TypedPosition
variable {G : Hypernet ops d [.term] []}

/-- Restarting an inserted focus has exactly the expected coordinate class. -/
theorem restart_class (p : TypedPosition G) (fg : FocusFree G) (hg : HoleFree G) :
    DeepStateClass.restart (DeepStateClass.ofState (p.realize fg hg)) =
      DeepStateClass.ofState (p.restart.realize fg hg) := by
  obtain ⟨a,eq⟩ := p.coordinate_recovery fg hg
  have h : (State.coordinate (p.realize fg hg)).restart.rename a = p.restart := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg (fun q => q.val.2) eq
  have iso := (State.coordinate (p.realize fg hg)).restart.realize_rename a
    (p.realize fg hg).focussed.underlying_focusFree
    ((p.realize fg hg).focussed.underlying_holeFree (p.realize fg hg).hole_free) fg hg
  rw [h] at iso
  exact Quotient.sound ⟨Focussed.DeepIso.ofIso iso⟩
end TypedPosition

namespace State
/-- The paper's search-history conclusion for a rooted actual state. Its restart
occurs on an initial execution, followed by a nonempty search suffix. -/
theorem rooted_revisit {s : State ops d} (rooted : Rooted kind s)
    (mode : s.focussed.mode ≠ .search) :
    ∃ a b, 0 < b ∧
      (DeepStateClass.searchMachine kind).Steps a (DeepStateClass.root (DeepStateClass.ofState s))
        (DeepStateClass.restart (DeepStateClass.ofState s)) ∧
      (DeepStateClass.searchMachine kind).Steps b (DeepStateClass.restart (DeepStateClass.ofState s))
        (DeepStateClass.ofState s) := by
  obtain ⟨n,run⟩ := rooted
  let G := s.focussed.underlying
  let fg := s.focussed.underlying_focusFree
  let hg := s.focussed.underlying_holeFree s.hole_free
  obtain ⟨q,trace,eq⟩ := (TypedPosition.initial G).class_steps_lift fg hg run
  have qm : q.val.1 ≠ .search := by
    obtain ⟨iso⟩ := Quotient.exact eq
    exact fun bad => mode (iso.mode.symm.trans bad)
  obtain ⟨a,b,_,positive,left,right⟩ := SearchHistory.revisit trace qm
  have restartEq := congrArg DeepStateClass.restart eq
  rw [q.restart_class fg hg] at restartEq
  refine ⟨a,b,positive,?_,?_⟩
  · rw [← restartEq]
    exact (TypedPosition.initial G).realize_steps fg hg q.restart left
  · rw [← restartEq,← eq]
    exact q.restart.realize_steps fg hg q right
end State
end Hypernets.Linear

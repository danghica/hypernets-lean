import Hypernets.Graph.DepthSearch

/-! The directed union of concrete recursive state classes over all finite depths. -/
namespace Hypernets.Linear.Unbounded
open Graph
variable {Op : Type} {ops : Operations Op}

/-- A finite presentation retains its depth, but the eventual state will not. -/
def Stage (ops : Operations Op) := (n : Nat) × DeepStateClass ops n

/-- Add one unused layer to a finite presentation. -/
def next (s : Stage ops) : Stage ops := ⟨s.1+1,DepthPadding.stateClass s.2⟩

/-- Repeated depth padding. -/
def advance : Nat → Stage ops → Stage ops
  | 0,s => s
  | k+1,s => next (advance k s)

theorem advance_add (i j : Nat) (s : Stage ops) :
    advance (i+j) s = advance j (advance i s) := by
  induction j with
  | zero => rfl
  | succ j ih => exact congrArg next ih

theorem advance_comm (i j : Nat) (s : Stage ops) :
    advance i (advance j s) = advance j (advance i s) := by
  rw [← advance_add,← advance_add,Nat.add_comm]

theorem advance_depth (k : Nat) (s : Stage ops) : (advance k s).1 = s.1+k := by
  induction k with
  | zero => rfl
  | succ k ih => change (advance k s).1+1 = _; omega

theorem next_injective {s t : Stage ops} (h : next s = next t) : s = t := by
  obtain ⟨n,s⟩ := s
  obtain ⟨m,t⟩ := t
  have hn : n+1 = m+1 := congrArg Sigma.fst h
  have hn : n = m := Nat.succ.inj hn
  subst m
  have hs : DepthPadding.stateClass s = DepthPadding.stateClass t := eq_of_heq (Sigma.mk.inj h).2
  exact congrArg (Sigma.mk n) (DepthPadding.stateClass_injective hs)

theorem advance_injective (k : Nat) {s t : Stage ops} (h : advance k s = advance k t) : s = t := by
  induction k with
  | zero => exact h
  | succ k ih => exact ih (next_injective h)

/-- Presentations agree when padding makes them the same recursive state class. -/
def Same (s t : Stage ops) : Prop := ∃ i j, advance i s = advance j t

theorem same_refl (s : Stage ops) : Same s s := ⟨0,0,rfl⟩

theorem same_symm {s t : Stage ops} : Same s t → Same t s := by
  rintro ⟨i,j,h⟩
  exact ⟨j,i,h.symm⟩

theorem same_trans {s t u : Stage ops} : Same s t → Same t u → Same s u := by
  rintro ⟨i,j,h⟩ ⟨k,l,g⟩
  refine ⟨i+k,l+j,?_⟩
  rw [advance_add,advance_add,h,advance_comm k j,g]

/-- The equivalence relation identifies only changes of depth presentation. -/
def stageSetoid (ops : Operations Op) : Setoid (Stage ops) :=
  ⟨Same,⟨same_refl,same_symm,same_trans⟩⟩

/-- A concrete state of arbitrary finite depth, modulo recursive names and padding. -/
def State (ops : Operations Op) := Quotient (stageSetoid ops)

def ofStage (s : Stage ops) : State ops := Quotient.mk _ s

def ofClass {n} (s : DeepStateClass ops n) : State ops := ofStage ⟨n,s⟩

theorem ofStage_advance (k : Nat) (s : Stage ops) : ofStage (advance k s) = ofStage s :=
  Quotient.sound ⟨0,k,rfl⟩

/-- Each fixed-depth state space embeds faithfully in the unbounded carrier. -/
theorem ofClass_injective {n} {s t : DeepStateClass ops n} (h : ofClass s = ofClass t) : s = t := by
  obtain ⟨i,j,h⟩ := Quotient.exact h
  have depths := congrArg Sigma.fst h
  have depths : n+i = n+j := (advance_depth i (⟨n,s⟩ : Stage ops)).symm.trans
    (depths.trans (advance_depth j (⟨n,t⟩ : Stage ops)))
  have ij : i = j := by simpa using depths
  subst j
  have eq := advance_injective i h
  exact eq_of_heq (Sigma.mk.inj eq).2

/-- A predicate on presentations that is unaffected by one padding step. -/
def Invariant (P : Stage ops → Prop) : Prop := ∀ s, P (next s) ↔ P s

theorem invariant_advance {P : Stage ops → Prop} (h : Invariant P) (k : Nat) (s : Stage ops) :
    P (advance k s) ↔ P s := by
  induction k with
  | zero => rfl
  | succ k ih => exact (h _).trans ih

theorem invariant_same {P : Stage ops → Prop} (h : Invariant P) {s t : Stage ops}
    (eq : Same s t) : P s ↔ P t := by
  obtain ⟨i,j,eq⟩ := eq
  rw [← invariant_advance h i s,← invariant_advance h j t,eq]

/-- Descend an actual invariant predicate to the unbounded carrier. -/
def predicate (P : Stage ops → Prop) (h : Invariant P) (s : State ops) : Prop :=
  Quotient.liftOn s P (fun _ _ eq => propext (invariant_same h eq))

def Initial : State ops → Prop := predicate (fun s => DeepStateClass.Initial s.2)
  (fun s => DepthPadding.class_initial_iff s.2)

def Final : State ops → Prop := predicate (fun s => DeepStateClass.Final s.2)
  (fun s => DepthPadding.class_final_iff s.2)

theorem initial_ofClass {n} (s : DeepStateClass ops n) : Initial (ofClass s) ↔ DeepStateClass.Initial s := Iff.rfl

theorem final_ofClass {n} (s : DeepStateClass ops n) : Final (ofClass s) ↔ DeepStateClass.Final s := Iff.rfl
end Hypernets.Linear.Unbounded

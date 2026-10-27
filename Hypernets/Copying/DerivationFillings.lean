import Hypernets.Copying.BoxPermutationInvariants
import Hypernets.Copying.ReverseFillings
import Hypernets.Copying.FillingPadding

/-! Interpret finite BPerm derivations by finite chains of the original recursive
filling certificates. A chain is synchronised by repeating its endpoint; no
transitivity property is imposed on the original filling relation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Recursive fillings preserve every primitive-label predicate preserved by
their actual template holes. The surrounding context need not satisfy it. -/
theorem DeepFilling.allLabels_iff {T : PreTemplate} (P : Primitive → Prop)
    (preserve : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H →
      (AllLabels P G ↔ AllLabels P H))
    {d I O} {C G H : Hypernet d I O} (pair : DeepFilling T C G H) :
    AllLabels P G ↔ AllLabels P H := by
  induction d generalizing I O with
  | zero =>
    cases pair with
    | expand C L R edges =>
      have each (e : C.Edge) : AllLabels P (L e) ↔ AllLabels P (R e) := by
        cases edges e with
        | retained l r =>
          constructor
          · intro h x; rw [r.only x,r.edge_label]; simpa only [l.edge_label] using h l.edge
          · intro h x; rw [l.only x,l.edge_label]; simpa only [r.edge_label] using h r.edge
        | filled h label rel => exact preserve rel
      exact ⟨fun h ⟨e,x⟩ => (each e).mp (fun y => h ⟨e,y⟩) x,
        fun h ⟨e,x⟩ => (each e).mpr (fun y => h ⟨e,y⟩) x⟩
  | succ d ih =>
    cases pair with
    | expand C L R edges =>
      have each (e : C.Edge) : AllLabels P (L e) ↔ AllLabels P (R e) := by
        cases edges e with
        | retained l r =>
          constructor
          · intro h x; rw [r.only x,r.edge_label]; simpa only [l.edge_label] using h l.edge
          · intro h x; rw [l.only x,l.edge_label]; simpa only [r.edge_label] using h r.edge
        | filled h label rel => exact preserve rel
        | boxed b label inner l r =>
          constructor
          · intro h x
            rw [r.only x,r.edge_label]
            apply (ih inner).mp
            have a := h l.edge
            rw [l.edge_label] at a
            exact a
          · intro h x
            rw [l.only x,l.edge_label]
            apply (ih inner).mpr
            have a := h r.edge
            rw [r.edge_label] at a
            exact a
      exact ⟨fun h ⟨e,x⟩ => (each e).mp (fun y => h ⟨e,y⟩) x,
        fun h ⟨e,x⟩ => (each e).mpr (fun y => h ⟨e,y⟩) x⟩

theorem FillingWitness.allLabels_iff {T : PreTemplate} (P : Primitive → Prop)
    (preserve : ∀ {d I O} {G H : Hypernet d I O}, T.Rel G H →
      (AllLabels P G ↔ AllLabels P H))
    {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H) :
    AllLabels P G ↔ AllLabels P H :=
  (allLabels_iso_iff P w.leftIso).symm.trans
    ((w.paired.allLabels_iff P preserve).trans (allLabels_iso_iff P w.rightIso))

namespace BoxPermutation

theorem filling_allLabels {d I O} {G H : Hypernet d I O}
    (w : FillingWitness template G H) (P : Primitive → Prop) :
    AllLabels P G ↔ AllLabels P H :=
  w.allLabels_iff (T := template) P (fun rel => rel.1.allLabels P)

/-- A finite sequence of original BPerm fillings, followed by reflexive steps.
The explicit bound permits synchronisation of any enumerated finite family. -/
structure FillingChain {d I O} (G H : Hypernet d I O) where
  length : Nat
  graph : Nat → Hypernet d I O
  start : graph 0 = G
  finish : ∀ n, length ≤ n → graph n = H
  step : ∀ n, FillingWitness template (graph n) (graph (n+1))

namespace FillingChain

theorem focusFree {d I O} {G H : Hypernet d I O} (c : FillingChain G H) (n : Nat) :
    FocusFree (c.graph n) := (c.step n).focusFree.1

theorem allLabels {d I O} {G H : Hypernet d I O} (c : FillingChain G H)
    (P : Primitive → Prop) (n : Nat) : AllLabels P G ↔ AllLabels P (c.graph n) := by
  induction n with
  | zero => rw [c.start]
  | succ n ih => exact ih.trans (filling_allLabels (c.step n) P)

/-- The empty chain still records the endpoint's required focus freedom. -/
def refl {d I O} (G : Hypernet d I O) (free : FocusFree G) : FillingChain G G where
  length := 0
  graph _ := G
  start := rfl
  finish _ _ := rfl
  step _ := FillingWitness.refl G free

/-- An original recursive filling is a chain of length one. -/
def single {d I O} {G H : Hypernet d I O} (w : FillingWitness template G H) :
    FillingChain G H where
  length := 1
  graph n := if n = 0 then G else H
  start := by simp
  finish n h := by simp [show n ≠ 0 by omega]
  step n := by
    by_cases h : n = 0
    · subst n; simpa using w
    · simpa [h] using FillingWitness.refl H w.focusFree.2

/-- Concatenation joins chains at their common graph, retaining every original
certificate rather than manufacturing a transitive filling certificate. -/
def trans {d I O} {G H K : Hypernet d I O}
    (c : FillingChain G H) (e : FillingChain H K) : FillingChain G K where
  length := c.length + e.length
  graph n := if n < c.length then c.graph n else e.graph (n-c.length)
  start := by
    by_cases h : 0 < c.length
    · simpa [h] using c.start
    · have eq : c.length = 0 := by omega
      simpa [h] using e.start.trans ((c.finish 0 (by omega)).symm.trans c.start)
  finish n h := by simp [show ¬ n < c.length by omega,e.finish (n-c.length) (by omega)]
  step n := by
    by_cases h : n+1 < c.length
    · simpa [h,show n < c.length by omega] using c.step n
    · by_cases hn : n < c.length
      · have eq : n+1 = c.length := by omega
        have endEq : c.graph (n+1) = e.graph (n+1-c.length) := by
          rw [c.finish (n+1) (by omega),eq,Nat.sub_self,e.start]
        simpa only [ite_eq_left hn,ite_eq_right h,endEq] using c.step n
      · have ar : n+1-c.length = (n-c.length)+1 := by omega
        simpa only [ite_eq_right hn,ite_eq_right h,ar] using e.step (n-c.length)

/-- Reverse a finite chain using the proved reversal of actual BPerm fillings. -/
noncomputable def symm {d I O} {G H : Hypernet d I O} (c : FillingChain G H) :
    FillingChain H G where
  length := c.length
  graph n := c.graph (c.length-n)
  start := by simpa using c.finish c.length (Nat.le_refl _)
  finish n h := by simpa [Nat.sub_eq_zero_of_le h] using c.start
  step n := by
    by_cases h : n < c.length
    · have eq : c.length-n = (c.length-(n+1))+1 := by omega
      simpa only [eq] using (reverseFilling (c.step (c.length-(n+1)))).witness
    · have hn : c.length ≤ n := by omega
      simpa [Nat.sub_eq_zero_of_le hn,Nat.sub_eq_zero_of_le (show c.length ≤ n+1 by omega)] using
        FillingWitness.refl (c.graph 0) (c.focusFree 0)

/-- Pointwise serial composition synchronises at the larger finite bound. -/
def serial {d I J O} {G G' : Hypernet d I J} {H H' : Hypernet d J O}
    (c : FillingChain G G') (e : FillingChain H H') :
    FillingChain (Serial.net G H) (Serial.net G' H') where
  length := max c.length e.length
  graph n := Serial.net (c.graph n) (e.graph n)
  start := by rw [c.start,e.start]
  finish n h := by rw [c.finish n (by omega),e.finish n (by omega)]
  step n := (c.step n).serial (e.step n)

def tensor {d I O J K} {G G' : Hypernet d I O} {H H' : Hypernet d J K}
    (c : FillingChain G G') (e : FillingChain H H') :
    FillingChain (Net.Tensor.net G H) (Net.Tensor.net G' H') where
  length := max c.length e.length
  graph n := Net.Tensor.net (c.graph n) (e.graph n)
  start := by rw [c.start,e.start]
  finish n h := by rw [c.finish n (by omega),e.finish n (by omega)]
  step n := (c.step n).tensor (e.step n)

/-- Each enumerated component's bound is below the sum, even if the finite
enumeration repeats entries. -/
theorem length_le_sum {A : Type} (f : A → Nat) (xs : List A) {a : A} (mem : a ∈ xs) :
    f a ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at mem
  | cons x xs ih =>
    simp only [List.mem_cons] at mem
    simp only [List.map_cons,List.sum_cons]
    rcases mem with eq | mem
    · subst a; omega
    · have h := ih mem; omega

/-- Finite parallel families advance simultaneously and then repeat endpoints.
This handles arbitrary enumeration carriers, not only binary tensor products. -/
def parallel {d : Nat} {A : Type} {I O : A → List Wire} {J K : List Wire}
    {G H : ∀ a, Hypernet d (I a) (O a)} (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration A) (c : ∀ a, FillingChain (G a) (H a)) :
    FillingChain (Net.Parallel.net G B finite) (Net.Parallel.net H B finite) where
  length := (finite.elements.map (fun a => (c a).length)).sum
  graph n := Net.Parallel.net (fun a => (c a).graph n) B finite
  start := by simp only [FillingChain.start]
  finish n h := by
    have eq : (fun a => (c a).graph n) = H := by
      funext a
      apply (c a).finish
      exact Nat.le_trans (length_le_sum (fun a => (c a).length) _ (finite.complete a)) h
    rw [eq]
  step n := FillingWitness.parallel B finite (fun a => (c a).step n)

def boxed {d n k h} {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (c : FillingChain G H) :
    FillingChain (box (bound := n) (freeVariables := k) G)
      (box (bound := n) (freeVariables := k) H) where
  length := c.length
  graph i := box (c.graph i)
  start := by rw [c.start]
  finish i h := by rw [c.finish i h]
  step i := (c.step i).boxed

def interfaces {d I O J K} {G H : Hypernet d I O}
    (c : FillingChain G H) (hi : I = J) (ho : O = K) :
    FillingChain (Translation.castInterfaces hi ho G) (Translation.castInterfaces hi ho H) where
  length := c.length
  graph i := Translation.castInterfaces hi ho (c.graph i)
  start := by rw [c.start]
  finish i h := by rw [c.finish i h]
  step i := (c.step i).interfaces hi ho

noncomputable def raise {d I O} {G H : Hypernet d I O} (c : FillingChain G H) :
    FillingChain (Copying.raise d G) (Copying.raise d H) where
  length := c.length
  graph i := Copying.raise d (c.graph i)
  start := by rw [c.start]
  finish i h := by rw [c.finish i h]
  step i := (c.step i).raise template_paddingClosed

def depthCast {d e I O} {G H : Hypernet d I O} (c : FillingChain G H) (eq : d = e) :
    FillingChain (Translation.castDepth eq G) (Translation.castDepth eq H) := by
  cases eq; exact c

noncomputable def pad {d I O} {G H : Hypernet d I O} (c : FillingChain G H) : (n : Nat) →
    FillingChain (Translation.pad d n G) (Translation.pad d n H)
  | 0 => c
  | n+1 => (c.pad n).raise

end FillingChain

/-- Every focus-free structural derivation has a finite interpretation by the
original recursive filling certificates. No observational relation is assumed. -/
theorem Derivation.fillingChain_exists {d I O} {G H : Hypernet d I O}
    (s : Derivation G H) (free : FocusFree G) : Nonempty (FillingChain G H) := by
  induction s with
  | iso f => exact ⟨.single ((FillingWitness.refl _ free).congr (DeepIso.refl _) f)⟩
  | rule s =>
    exact ⟨.single (FillingWitness.of_rel 0 ⟨.witness (DeepIso.refl _) s (DeepIso.refl _),free⟩)⟩
  | symm s ih =>
    obtain ⟨c⟩ := ih (s.focusFree.mpr free)
    exact ⟨c.symm⟩
  | trans s t ih jh =>
    obtain ⟨c⟩ := ih free
    obtain ⟨e⟩ := jh (s.focusFree.mp free)
    exact ⟨c.trans e⟩
  | serial s t ih jh =>
    have parts := (Serial.allLabels_iff _ _ _).mp free
    obtain ⟨c⟩ := ih parts.1
    obtain ⟨e⟩ := jh parts.2
    exact ⟨c.serial e⟩
  | tensor s t ih jh =>
    have parts := (Net.Tensor.labels_iff _ _ (LabelAll _ _)).mp free
    obtain ⟨c⟩ := ih parts.1
    obtain ⟨e⟩ := jh parts.2
    exact ⟨c.tensor e⟩
  | parallel B finite s ih =>
    exact ⟨.parallel B finite (fun a => Classical.choice (ih a (fun e => free ⟨a,e⟩)))⟩
  | box s ih =>
    obtain ⟨c⟩ := ih (free (0 : Fin 1))
    exact ⟨c.boxed⟩
  | interfaces hi ho s ih =>
    obtain ⟨c⟩ := ih ((Translation.allLabels_cast _ hi ho _).mp free)
    exact ⟨c.interfaces hi ho⟩
  | raise s ih =>
    obtain ⟨c⟩ := ih ((allLabels_raise_iff _ _ _).mp free)
    exact ⟨c.raise⟩

noncomputable def Derivation.fillingChain {d I O} {G H : Hypernet d I O}
    (s : Derivation G H) (free : FocusFree G) : FillingChain G H :=
  Classical.choice (s.fillingChain_exists free)

end BoxPermutation
end Hypernets.Copying

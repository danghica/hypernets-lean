import Hypernets.Copying.AtomEqualityResolution

/-! Reference comparison is determined by resolved store identity, independently
of trace witnesses and contraction-tree presentations. -/
namespace Hypernets.Copying.AtomEquality
open Graph

/-- A boolean justified by two successful store lookups, not by stored contents. -/
def Outcome {d I O} (G : Hypernet d I O) (a b : G.Edge) (result : Bool) : Prop :=
  ∃ s t n m, StoreTrace.Resolves G a s n ∧ StoreTrace.Resolves G b t m ∧
    (result = true ↔ s = t)

/-- All successful lookup witnesses give the same boolean, even in a cyclic host. -/
theorem outcome_unique {d I O} {G : Hypernet d I O} {a b result other}
    (x : Outcome G a b result) (y : Outcome G a b other) : result = other := by
  obtain ⟨s,t,n,m,ls,rt,h⟩ := x
  obtain ⟨u,v,j,k,lu,rv,h'⟩ := y
  have su := (StoreTrace.resolves_unique ls lu).1
  have tv := (StoreTrace.resolves_unique rt rv).1
  subst u; subst v
  cases result <;> cases other <;> simp_all

/-- Attaching the matched fragment preserves the identity comparison. -/
theorem outcome_insert {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b result}
    (out : Outcome G a b result) : Outcome (C.plug hole G) (.inr a) (.inr b) result := by
  obtain ⟨s,t,n,m,left,right,eq⟩ := out
  exact ⟨.inr s,.inr t,n,m,StoreTrace.resolves_insert C hole G left,
    StoreTrace.resolves_insert C hole G right,eq.trans (by simp)⟩

/-- No successful alternative routing through the host can flip the comparison. -/
theorem inserted_outcome_unique {d I O} (C : Hypernet d I O) (hole : C.Edge)
    (G : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole))
      ((alphabet d).signature.output (C.edgeLabel hole))) {a b result other}
    (out : Outcome G a b result) (host : Outcome (C.plug hole G) (.inr a) (.inr b) other) :
    result = other := outcome_unique (outcome_insert C hole G out) host

namespace Same

theorem true_before {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Outcome (before T d) (beforeLeft T d) (beforeRight T d) true := by
  obtain ⟨n,a,_⟩ := resolves_left T d
  obtain ⟨m,b,_⟩ := resolves_right T d
  exact ⟨_,_,n,m,a,b,by simp⟩

theorem true_after {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Outcome (after T d) (afterLeft T d) (afterRight T d) true := by
  obtain ⟨n,_,a⟩ := resolves_left T d
  obtain ⟨m,_,b⟩ := resolves_right T d
  exact ⟨_,_,n,m,a,b,by simp⟩

theorem cannot_return_false {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    ¬ Outcome (before T d) (beforeLeft T d) (beforeRight T d) false := by
  intro bad; have eq := outcome_unique (true_before T d) bad; cases eq
end Same
namespace Different

theorem stores_distinct_before {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    beforeStore T U d ≠ beforeStoreRight T U d := by
  intro eq; have bad := congrArg Sigma.fst eq; cases bad

theorem stores_distinct_after {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    afterStore T U d ≠ afterStoreRight T U d := by
  intro eq; have bad := congrArg Sigma.fst eq; cases bad

theorem false_before {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Outcome (before T U d) (beforeLeft T U d) (beforeRight T U d) false := by
  obtain ⟨j,a,_⟩ := resolves_left T U d
  obtain ⟨k,b,_⟩ := resolves_right T U d
  exact ⟨_,_,j,k,a,b,by simp [stores_distinct_before T U d]⟩

theorem false_after {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Outcome (after T U d) (afterLeft T U d) (afterRight T U d) false := by
  obtain ⟨j,_,a⟩ := resolves_left T U d
  obtain ⟨k,_,b⟩ := resolves_right T U d
  exact ⟨_,_,j,k,a,b,by simp [stores_distinct_after T U d]⟩

theorem cannot_return_true {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    ¬ Outcome (before T U d) (beforeLeft T U d) (beforeRight T U d) true := by
  intro bad; have eq := outcome_unique (false_before T U d) bad; cases eq
end Different
end Hypernets.Copying.AtomEquality

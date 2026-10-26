import Hypernets.Copying.CopyExecution

/-! Copying a reference duplicates its instance but retains one shared store. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph

/-- Attach the single original store beyond the copy rule's atom distributor. -/
def sharedStore {n} (T : ContractionTree .term (n+1)) :
    Hypernet 0 (List.replicate (n+1) .term) [.term] :=
  Serial.net (after (k := 0) (h := 1) T (primitiveNet 0 .instanceEdge)) (primitiveNet 0 .store)

def sharedLeft {n} (T : ContractionTree .term (n+1)) : (sharedStore T).Edge :=
  Serial.leftEdge _ _ (leftEdge T _ (0 : Fin 1))
def sharedRight {n} (T : ContractionTree .term (n+1)) : (sharedStore T).Edge :=
  Serial.leftEdge _ _ (rightEdge T _ (0 : Fin 1))
def sharedCell {n} (T : ContractionTree .term (n+1)) : (sharedStore T).Edge :=
  Serial.rightEdge _ _ (0 : Fin 1)
def sharedContraction {n} (T : ContractionTree .term (n+1)) (i : Fin 3) : (sharedStore T).Edge :=
  Serial.leftEdge _ _ (Serial.rightEdge _ _ ⟨true,⟨(0 : Fin 1),i⟩⟩)

theorem shared_instance_labels {n} (T : ContractionTree .term (n+1)) :
    (sharedStore T).edgeLabel (sharedLeft T) = primitiveLabel 0 .instanceEdge ∧
    (sharedStore T).edgeLabel (sharedRight T) = primitiveLabel 0 .instanceEdge := ⟨rfl,rfl⟩

theorem shared_cell_label {n} (T : ContractionTree .term (n+1)) :
    (sharedStore T).edgeLabel (sharedCell T) = primitiveLabel 0 .store := rfl

/-- Both instance outputs meet the same lower atom contraction. -/
theorem shared_left_hop {n} (T : ContractionTree .term (n+1)) :
    StoreTrace.Hop (sharedStore T) (sharedLeft T) (sharedContraction T 2) := by
  constructor
  · exact Or.inl rfl
  · refine ⟨((sharedStore T).target (sharedLeft T))[0]'(by change 0 < 1; decide),?_,?_⟩
    · change _ ∈ [_]; exact List.mem_cons_self
    · change _ ∈ [_,_]; exact List.mem_cons_self

theorem shared_right_hop {n} (T : ContractionTree .term (n+1)) :
    StoreTrace.Hop (sharedStore T) (sharedRight T) (sharedContraction T 2) := by
  constructor
  · exact Or.inl rfl
  · refine ⟨((sharedStore T).target (sharedRight T))[0]'(by change 0 < 1; decide),?_,?_⟩
    · change _ ∈ [_]; exact List.mem_cons_self
    · change _ ∈ [_,_]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem shared_root_hop {n} (T : ContractionTree .term (n+1)) :
    StoreTrace.Hop (sharedStore T) (sharedContraction T 2) (sharedContraction T 1) := by
  constructor
  · exact Or.inr (Or.inl rfl)
  · refine ⟨((sharedStore T).target (sharedContraction T 2))[0]'(by change 0 < 1; decide),?_,?_⟩
    · change _ ∈ [_]; exact List.mem_cons_self
    · change _ ∈ [_,_]; exact List.mem_cons_of_mem _ List.mem_cons_self

theorem shared_store_hop {n} (T : ContractionTree .term (n+1)) :
    StoreTrace.Hop (sharedStore T) (sharedContraction T 1) (sharedCell T) := by
  constructor
  · exact Or.inr (Or.inl rfl)
  · refine ⟨((sharedStore T).target (sharedContraction T 1))[0]'(by change 0 < 1; decide),?_,?_⟩
    · change _ ∈ [_]; exact List.mem_cons_self
    · change _ ∈ [_]; exact List.mem_cons_self

/-- Exact three-hop resolution of both copies to the same original cell. -/
theorem shared_resolves {n} (T : ContractionTree .term (n+1)) :
    StoreTrace.Resolves (sharedStore T) (sharedLeft T) (sharedCell T) 3 ∧
    StoreTrace.Resolves (sharedStore T) (sharedRight T) (sharedCell T) 3 := by
  constructor
  · exact ⟨.step (shared_left_hop T) (.step (shared_root_hop T) (.step (shared_store_hop T) (.refl _))),rfl⟩
  · exact ⟨.step (shared_right_hop T) (.step (shared_root_hop T) (.step (shared_store_hop T) (.refl _))),rfl⟩

/-- Neither copy can resolve to a different cell or use a different successful cost. -/
theorem shared_resolves_unique {n} (T : ContractionTree .term (n+1)) {e m}
    (run : StoreTrace.Resolves (sharedStore T) (sharedLeft T) e m ∨
      StoreTrace.Resolves (sharedStore T) (sharedRight T) e m) : e = sharedCell T ∧ m = 3 := by
  rcases run with run | run
  · exact StoreTrace.resolves_unique run (shared_resolves T).1
  · exact StoreTrace.resolves_unique run (shared_resolves T).2
end Hypernets.Copying.CopyRule

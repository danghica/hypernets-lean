import Hypernets.Copying.ExpansionSearch

/-! One-way fillings and the output-closure obstruction needed by specimens. -/
namespace Hypernets.Copying
open Graph

/-- No term output is connected to an input by an operation-only path. -/
def OneWay {d I O} (G : Hypernet d I O) : Prop :=
  ∀ j : Fin O.length, G.vertexLabel (.output j) = .term →
    ¬ Search.OperationReachable G (.output j)

namespace Search.Expansion
variable {d I O} (C : Hypernet d I O)
    (H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
open Net.Expansion

theorem insert_not_input (e : C.Edge) {v : (H e).Vertex} (no : ¬ v.IsInput) :
    ¬ (insert C H e v).IsInput := by
  obtain ⟨f,mem⟩ := ((H e).target_coverage v).mpr no
  exact (C.expand H).target_not_input (e := ⟨e,f⟩) (List.mem_map_of_mem mem)

/-- Operation reachability at an inserted vertex reflects into that component.
No acyclicity, injective attachment, or properties of the other fillings are assumed. -/
theorem extract_at (e : C.Edge) {w : (C.expand H).Vertex}
    (reach : OperationReachable (C.expand H) w) :
    ∀ v : (H e).Vertex, insert C H e v = w → OperationReachable (H e) v := by
  induction reach with
  | input i =>
    intro v eq
    by_cases input : v.IsInput
    · cases v with
      | input j => exact .input j
      | internal => contradiction
      | output => contradiction
    · exact False.elim (insert_not_input C H e input (eq ▸ trivial))
  | @argument a o root w label source parent member ih =>
    intro v eq
    by_cases input : v.IsInput
    · cases v with
      | input j => exact .input j
      | internal => contradiction
      | output => contradiction
    · obtain ⟨f,ft⟩ := ((H e).target_coverage v).mpr input
      have inserted : insert C H e v ∈ (C.expand H).target ⟨e,f⟩ := List.mem_map_of_mem ft
      have same : a = ⟨e,f⟩ := (C.expand H).target_unique member (eq ▸ inserted)
      subst a
      have localLabel : (H e).edgeLabel f = primitiveLabel d (.operation o) := label
      have len : ((H e).source f).length = 1 := by rw [(H e).source_length,localLabel,primitive_input]; rfl
      obtain ⟨r,src⟩ := List.length_eq_one_iff.mp len
      have srceq : insert C H e r = root := by
        change ((H e).source f).map (insert C H e) = [root] at source
        rw [src] at source
        exact (List.cons.inj source).1
      exact .argument localLabel src (ih r srceq) ft

/-- A one-way component blocks rooted search at every attached term output. -/
theorem oneWay_target (e : C.Edge) (one : OneWay (H e)) {v : C.Vertex}
    (term : C.vertexLabel v = .term) (mem : v ∈ C.target e) :
    ¬ OperationReachable (C.expand H) (host C H v) := by
  obtain ⟨j,eq⟩ := (C.mem_target_iff_port e v).mp mem
  subst v
  have outputTerm : (H e).vertexLabel (.output j) = .term :=
    (C.targetPort_label e j).symm.trans term
  exact fun reach => one j outputTerm (extract_at C H e reach (.output j) rfl)

/-- Output closure is a per-hole disjunction; its choice need not be uniform. -/
def OutputClosedPair (K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
    ((alphabet d).signature.output (C.edgeLabel e))) : Prop :=
  ∀ e h, C.edgeLabel e = primitiveLabel d (.hole h) → OneWay (H e) ∨ OneWay (K e)

theorem not_exiting {K} (closed : OutputClosedPair C H K) (p : Position C)
    (term : C.vertexLabel p.2 = .term) {i}
    (left : RootedFrom (C.expand H) i (position C H p))
    (right : RootedFrom (C.expand K) i (position C K p)) : ¬ Exiting C p := by
  rintro ⟨e,h,label,mem⟩
  rcases closed e h label with one | one
  · exact oneWay_target C H e one term mem (rooted_reachable left)
  · exact oneWay_target C K e one term mem (rooted_reachable right)

theorem settled_away {K} (closed : OutputClosedPair C H K) (p : Position C)
    (term : C.vertexLabel p.2 = .term) {i}
    (left : RootedFrom (C.expand H) i (position C H p))
    (right : RootedFrom (C.expand K) i (position C K p))
    (settled : p.1 = .backtrack ∨ (p.1 = .search ∧ ¬ Entering C p)) : ¬ Boundary C p := by
  rintro (⟨mode,enter⟩ | ⟨_,exit⟩)
  · rcases settled with back | ⟨_,no⟩
    · cases back.symm.trans mode
    · exact no enter
  · exact not_exiting C H closed p term left right exit

/-- Search can produce rewrite mode only at a genuine retained head, never a hole. -/
theorem remote_target {p q : Position C} (step : Step C p q) : q.1 ≠ .rewrite ∨ ¬ Entering C q := by
  have avoid {e prim v} (label : C.edgeLabel e = primitiveLabel d prim)
      (notHole : ∀ h, prim ≠ .hole h) (mem : v ∈ C.source e) : ¬ Entering C (.rewrite,v) := by
    rintro ⟨f,h,hole,member⟩
    exact notHole h (primitiveLabel_injective d (label.symm.trans ((congrArg C.edgeLabel (C.source_unique mem member)).trans hole)))
  cases step with
  | search e prim v q label src result =>
    cases prim with
    | operation o =>
      simp only [enter] at result
      split at result
      · cases result
        exact .inr (by simpa [Entering] using avoid label (fun _ h => by cases h) src)
      · obtain ⟨w,_,eq⟩ := Option.map_eq_some_iff.mp result; subst q
        exact .inl (by simp)
    | contraction s => cases s <;> simp only [enter] at result
                       · cases result; exact .inr (avoid label (fun _ h => by cases h) src)
                       · cases result
    | instanceEdge => cases result; exact .inl (by simp)
    | weakening s => cases result
    | store => cases result
    | hole h => cases result
    | focus m => cases result
  | backtrack e o root v i q label src bound arg result =>
    simp only [resume] at result
    split at result
    · obtain ⟨w,_,eq⟩ := Option.map_eq_some_iff.mp result; subst q
      exact .inl (by simp)
    · cases result
      exact .inr (by simpa [Entering] using avoid label (fun _ h => by cases h) (by simp [src]))
end Search.Expansion
end Hypernets.Copying

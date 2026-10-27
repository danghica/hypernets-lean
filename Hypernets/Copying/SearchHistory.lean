import Hypernets.Copying.IntrinsicRefocusing

/-! Exact search history at operation sources, including returns from evaluated arguments. -/
namespace Hypernets.Copying.Search
open Graph
variable {d I O} {G : Hypernet d I O} {i : Fin I.length}

def Visit (G : Hypernet d I O) (i : Fin I.length) (n : Nat) (p : Position G) (v : G.Vertex) : Prop :=
  ∃ a b, n = a+b ∧ (machine G).Steps a (.search,.input i) (.search,v) ∧
    (machine G).Steps b (.search,v) p

inductive HistoryStack (G : Hypernet d I O) (i : Fin I.length) (P : G.Vertex → Prop) : G.Vertex → Prop where
  | root : HistoryStack G i P (.input i)
  | argument {e o root v} (label : G.edgeLabel e = primitiveLabel d (.operation o))
      (source : G.source e = [root]) (parent : HistoryStack G i P root)
      (visited : P root) (member : v ∈ G.target e) : HistoryStack G i P v

theorem HistoryStack.mono {P Q : G.Vertex → Prop} (f : ∀ v, P v → Q v) {v}
    (stack : HistoryStack G i P v) : HistoryStack G i Q v := by
  induction stack with
  | root => exact .root
  | argument label source parent visit member ih => exact .argument label source ih (f _ visit) member

theorem HistoryStack.parent {P : G.Vertex → Prop} {v e root}
    (stack : HistoryStack G i P v) (src : G.source e = [root]) (mem : v ∈ G.target e) :
    HistoryStack G i P root ∧ P root := by
  cases stack with
  | root => exact False.elim (G.target_not_input mem trivial)
  | argument label source parent visit member =>
    have same := (List.cons.inj (src.symm.trans ((congrArg G.source (G.target_unique mem member)).trans source))).1
    exact same ▸ ⟨parent,visit⟩

theorem Visit.step {n p q v} (visit : Visit G i n p v) (step : Step G p q) : Visit G i (n+1) q v := by
  obtain ⟨a,b,count,left,right⟩ := visit
  exact ⟨a,b+1,by omega,left,right.append (.cons step (.zero _))⟩

theorem Visit.current {n v} (run : (machine G).Steps n (.search,.input i) (.search,v)) :
    Visit G i n (.search,v) v := ⟨n,0,by omega,run,.zero _⟩

def History (G : Hypernet d I O) (i : Fin I.length) (n : Nat) (p : Position G) : Prop :=
  HistoryStack G i (Visit G i n p) p.2 ∧ Visit G i n p p.2

theorem history_step {n p q} (h : History G i n p) (step : Step G p q) : History G i (n+1) q := by
  have run : (machine G).Steps n (.search,.input i) p := by
    obtain ⟨a,b,count,left,right⟩ := h.2
    exact count ▸ left.append right
  have extended := run.append (Machine.Steps.cons step (.zero _))
  have stack := h.1.mono (fun _ visit => visit.step step)
  have visit := h.2.step step
  cases step with
  | search e p v q label src result =>
    cases p with
    | operation o =>
      have source := operation_source label src
      simp only [enter] at result
      split at result
      · cases result; exact ⟨stack,visit⟩
      · obtain ⟨w,mem,eq⟩ := Option.map_eq_some_iff.mp result
        subst q
        exact ⟨.argument label source stack visit (List.mem_of_getElem? mem),Visit.current extended⟩
    | contraction s => cases s <;> simp only [enter] at result
                       · cases result; exact ⟨stack,visit⟩
                       · cases result
    | instanceEdge => cases result; exact ⟨stack,visit⟩
    | weakening s => cases result
    | store => cases result
    | hole h => cases result
    | focus m => cases result
  | backtrack e o root v j q label src bound arg result =>
    obtain ⟨parent,earlier⟩ := stack.parent src (List.mem_of_getElem? arg)
    simp only [resume] at result
    split at result
    · obtain ⟨w,mem,eq⟩ := Option.map_eq_some_iff.mp result
      subst q
      exact ⟨.argument label src parent earlier (List.mem_of_getElem? mem),Visit.current extended⟩
    · cases result; exact ⟨parent,earlier⟩

theorem history_run {n s t} (run : (machine G).Steps n s t) {m}
    (h : History G i m s) : History G i (m+n) t := by
  induction run generalizing m with
  | zero => simpa using h
  | cons step run ih =>
    simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (history_step h step)

theorem history {n p} (run : (machine G).Steps n (.search,.input i) p) : History G i n p := by
  have initial : History G i 0 (.search,.input i) := ⟨.root,Visit.current (.zero _)⟩
  simpa using history_run run initial

/-- The original exact run splits at an earlier search visit to its final token wire. -/
theorem revisit {n p} (run : (machine G).Steps n (.search,.input i) p) (mode : p.1 ≠ .search) :
    ∃ a b, n = a+b ∧ 0 < b ∧
      (machine G).Steps a (.search,.input i) (.search,p.2) ∧
      (machine G).Steps b (.search,p.2) p := by
  obtain ⟨a,b,count,left,right⟩ := (history run).2
  refine ⟨a,b,count,?_,left,right⟩
  cases b with
  | zero => exact False.elim (mode (congrArg Prod.fst right.zero_eq).symm)
  | succ b => omega
end Hypernets.Copying.Search

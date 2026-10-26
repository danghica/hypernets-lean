import Hypernets.Copying.FullRenamingExamples

/-! The copying UAM's intrinsic search rules, in token coordinates on actual
copying hypernets. Copy and compute transitions are separate unfinished phases. -/
namespace Hypernets.Copying
open Graph

/-- Only term arguments are searched; lambda's thunk output is skipped. -/
def Operation.arguments : Operation → Nat
  | .const _ | .lam => 0
  | .app | .binary _ => 2
  | .unary _ => 1

theorem primitiveLabel_injective (d : Nat) {p q : Primitive}
    (eq : primitiveLabel d p = primitiveLabel d q) : p = q := by
  cases d with
  | zero => exact congrArg ULift.down eq
  | succ d => exact Sum.inl.inj eq

namespace Search
abbrev Position {d I O} (G : Hypernet d I O) := Focus × G.Vertex

/-- Figure 9 operation entry and Figure 18 contraction/instance interactions.
In particular atom contraction, weakening, stores and holes have no search-entry rule. -/
def enter {V : Type} (p : Primitive) (v : V) (targets : List V) : Option (Focus × V) :=
  match p with
  | .operation o => if o.arguments = 0 then some (o.kind.finish,v) else
      (targets[0]?).map (fun w => (.search,w))
  | .contraction .term => some (.rewrite,v)
  | .instanceEdge => some (.backtrack,v)
  | _ => none

/-- Return from argument i: search the next term argument or finish the operation.
The argument bound is enforced by Step.backtrack, not guessed from list length. -/
def resume {V : Type} (o : Operation) (root : V) (targets : List V) (i : Nat) : Option (Focus × V) :=
  if i+1 < o.arguments then (targets[i+1]?).map (fun w => (.search,w))
  else some (o.kind.finish,root)

/-- Actual edge incidence, label and argument-position witnesses for intrinsic search. -/
inductive Step {d I O} (G : Hypernet d I O) : Position G → Position G → Prop where
  | search (e : G.Edge) (p : Primitive) (v : G.Vertex) (t : Position G)
      (label : G.edgeLabel e = primitiveLabel d p) (source : v ∈ G.source e)
      (result : enter p v (G.target e) = some t) : Step G (.search,v) t
  | backtrack (e : G.Edge) (o : Operation) (root v : G.Vertex) (i : Nat) (t : Position G)
      (label : G.edgeLabel e = primitiveLabel d (.operation o)) (source : G.source e = [root])
      (bound : i < o.arguments) (argument : (G.target e)[i]? = some v)
      (result : resume o root (G.target e) i = some t) : Step G (.backtrack,v) t

/-- Entry computations commute with every vertex map, including context attachment maps. -/
theorem enter_map {V W : Type} (f : V → W) (p : Primitive) (v : V) (vs : List V) :
    enter p (f v) (vs.map f) = (enter p v vs).map (fun x => (x.1,f x.2)) := by
  cases p with
  | operation o => simp only [enter]; split <;> simp [List.getElem?_map,Option.map_map,Function.comp_def]
  | contraction s => cases s <;> rfl
  | _ => rfl

theorem resume_map {V W : Type} (f : V → W) (o : Operation) (v : V) (vs : List V) (i : Nat) :
    resume o (f v) (vs.map f) i = (resume o v vs i).map (fun x => (x.1,f x.2)) := by
  simp only [resume]
  split <;> simp [List.getElem?_map,Option.map_map,Function.comp_def]

/-- Determinism uses graph incidence uniqueness and ordered, duplicate-free arguments. -/
theorem result_unique {d I O} {G : Hypernet d I O} {s s' t u : Position G}
    (a : Step G s t) (b : Step G s' u) (eq : s = s') : t = u := by
  cases a with
  | search e p v t label src result =>
    cases b with
    | search f q w u label' src' result' =>
      have vw := (Prod.mk.inj eq).2
      subst w
      have ef := G.source_unique src src'
      subst f
      have pq := primitiveLabel_injective d (label.symm.trans label')
      subst q
      exact Option.some.inj (result.symm.trans result')
    | backtrack => cases (Prod.mk.inj eq).1
  | backtrack e o root v i t label src bound arg result =>
    cases b with
    | search => cases (Prod.mk.inj eq).1
    | backtrack f q root' w j u label' src' bound' arg' result' =>
      have vw := (Prod.mk.inj eq).2
      subst w
      have ef := G.target_unique (List.mem_of_getElem? arg) (List.mem_of_getElem? arg')
      subst f
      have oq := Primitive.operation.inj (primitiveLabel_injective d (label.symm.trans label'))
      subst q
      have rr := (List.cons.inj (src.symm.trans src')).1
      subst root'
      have ij := (G.target_nodup e).eq_of_getElem?_eq (List.getElem?_eq_some_iff.mp arg).1 (arg.trans arg'.symm)
      subst j
      exact Option.some.inj (result.symm.trans result')

theorem deterministic {d I O} {G : Hypernet d I O} {s t u : Position G}
    (a : Step G s t) (b : Step G s u) : t = u := result_unique a b rfl

theorem no_rewrite {d I O} {G : Hypernet d I O} {v : G.Vertex} {t} : ¬ Step G (.rewrite,v) t := by
  intro step; cases step

theorem final_no_step {d I O} {G : Hypernet d I O} {v : G.Vertex} (input : v.IsInput) {t} :
    ¬ Step G (.backtrack,v) t := by
  intro step
  cases step with
  | backtrack e o root v i t label src bound arg result => exact G.target_not_input (List.mem_of_getElem? arg) input

/-- Terminal search phases have a unique endpoint and exact length. -/
theorem terminal_run_unique {d I O} {G : Hypernet d I O} {s t u : Position G} {n m}
    (a : Trace (Step G) s t n) (b : Trace (Step G) s u m)
    (ht : Terminal (Step G) t) (hu : Terminal (Step G) u) : t = u ∧ n = m :=
  Trace.terminal_unique (R := Step G) (fun a b => deterministic a b) a b ht hu
end Search
end Hypernets.Copying

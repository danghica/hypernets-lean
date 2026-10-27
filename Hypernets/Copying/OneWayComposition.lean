import Hypernets.Copying.BPermRewriteClassification

/-! Output-closure tools for the actual operational pre-templates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- If all outputs are atom or thunk wires, the one-way condition is immediate. -/
theorem oneWay_of_stable_outputs {d I O} (G : Hypernet d I O)
    (outputs : ∀ i : Fin O.length, StableOutput O[i]) : OneWay G := by
  intro j term
  have h := outputs j
  change O[j] = .term at term
  rw [term] at h
  exact False.elim h

namespace Search.OperationReachable
/-- Ordered recursive isomorphism transports each operation-only path. -/
theorem map_iso {d I O} {G H : Hypernet d I O} (f : DeepIso G H) {v}
    (reach : Search.OperationReachable G v) : Search.OperationReachable H (Port.map f.vertices.toFun v) := by
  induction reach with
  | input i => exact .input i
  | @argument e o root v label source parent member ih =>
    refine .argument ((Search.primitive_equiv (f.edge_label e) _).mp label) ?_ ih ?_
    · rw [← f.source,source]; rfl
    · rw [← f.target]; exact List.mem_map_of_mem member
end Search.OperationReachable

namespace OneWay

theorem iso_iff {d I O} {G H : Hypernet d I O} (f : DeepIso G H) : OneWay G ↔ OneWay H := by
  constructor
  · intro one j term reach; exact one j term (reach.map_iso f.symm)
  · intro one j term reach; exact one j term (reach.map_iso f)

/-- A serial continuation that blocks operation-only paths still blocks them
after arbitrary attachment on its input side. -/
theorem serial_right {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    (one : OneWay H) : OneWay (Serial.net G H) := by
  intro j term reach
  have localReach := Search.Expansion.extract_at (Serial.pattern d I J K) (Serial.filling G H) true reach
  cases d
  all_goals apply one j term (localReach (.output j) _)
  all_goals simp [Net.Expansion.insert, Serial.pattern, Net.targetPort, Net.Expansion.host, Port.map]

/-- A box is one-way regardless of its body, since its input is a thunk. -/
theorem box {d n k h} (B : Hypernet d [.term] (environmentInterface (n+k) h)) :
    OneWay (Copying.box (bound := n) (freeVariables := k) B) :=
  oneWay_of_no_term_inputs _ (by
    intro i eq
    have hi : i = 0 := Fin.ext (by have ht : i.val < 1 := i.isLt; change i.val = 0; omega)
    subst i
    cases eq)

end OneWay

namespace Search.Parallel
variable {d A} {I O : A → List Wire} (G : ∀ a, Hypernet d (I a) (O a))
    {J K} (B : Net.Parallel.Boundary I O J K) (finite : Enumeration A)

/-- Operation reachability in a parallel component cannot arrive from another
component, even under an arbitrary typed boundary shuffle. -/
theorem extract {v} (reach : OperationReachable (Net.Parallel.net G B finite) v) :
    ∀ a (x : (G a).Vertex), Net.Parallel.embed G B a x = v → OperationReachable (G a) x := by
  induction reach with
  | input i =>
    intro a x eq
    cases x with
    | input j => exact .input j
    | internal j => cases eq
    | output j => cases eq
  | @argument e o root v label source parent member ih =>
    intro a x eq
    obtain ⟨y,hy,ey⟩ := List.mem_map.mp member
    have same : (⟨e.1,y⟩ : Σ a, (G a).Vertex) = ⟨a,x⟩ :=
      (Net.Parallel.vertices G B).injective (ey.trans eq.symm)
    have tags := congrArg Sigma.fst same
    obtain ⟨b,e⟩ := e
    dsimp at tags; subst b
    have xy : y = x := Net.Parallel.embed_injective G B a (ey.trans eq.symm)
    subst y
    have localLabel : (G a).edgeLabel e = primitiveLabel d (.operation o) := label
    have len : ((G a).source e).length = 1 := by rw [(G a).source_length,localLabel,primitive_input]; rfl
    obtain ⟨r,src⟩ := List.length_eq_one_iff.mp len
    have rootEq : Net.Parallel.embed G B a r = root := by
      change ((G a).source e).map (Net.Parallel.embed G B a) = [root] at source
      rw [src] at source
      exact (List.cons.inj source).1
    exact .argument localLabel src (ih a r rootEq) hy
end Search.Parallel

namespace OneWay
/-- Independent components cannot create an operation-only path between them. -/
theorem parallel {d A} {I O : A → List Wire} (G : ∀ a, Hypernet d (I a) (O a))
    {J K} (B : Net.Parallel.Boundary I O J K) (finite : Enumeration A)
    (one : ∀ a, OneWay (G a)) : OneWay (Net.Parallel.net G B finite) := by
  intro j term reach
  let x := B.outputs.invFun j
  have eq : Net.Parallel.embed G B x.1 (.output x.2) = (.output j : (Net.Parallel.net G B finite).Vertex) :=
    congrArg Port.output (B.outputs.right_inv j)
  have typed : (G x.1).vertexLabel (.output x.2) = .term := by
    have h := Net.Parallel.embed_label G B x.1 (.output x.2)
    rw [eq] at h
    exact h.symm.trans term
  exact one x.1 x.2 typed (Search.Parallel.extract G B finite reach x.1 (.output x.2) eq)

theorem tensor {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (g : OneWay G) (h : OneWay H) : OneWay (Net.Tensor.net G H) := by
  apply parallel
  intro b; cases b
  · exact g
  · exact h
end OneWay
end Hypernets.Copying

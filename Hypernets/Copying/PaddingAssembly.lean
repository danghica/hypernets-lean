import Hypernets.Copying.ContextDepth

/-! One-step padding commutes with the original graph assembly constructors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Padding
open Graph

/-- Padding can be performed on either side of literal serial assembly. -/
noncomputable def serial_graph {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) :
    Net.Iso (graph (Serial.net G H)) (Serial.net (graph G) (graph H)) := by
  cases d with
  | zero =>
    exact {
      vertices := {
        toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        left_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl
        right_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl }
      edges := {
        toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
        right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
      internal_label v := by rcases v with v | ⟨a,v⟩; rfl; cases a <;> rfl
      edge_label x := by rcases x with ⟨a,f⟩; cases a <;> rfl
      source x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.source f).map _).map _ = (G.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.source f).map _).map _ = (H.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
      target x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.target f).map _).map _ = (G.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.target f).map _).map _ = (H.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
    }
  | succ d =>
    exact {
      vertices := {
        toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        left_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl
        right_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl }
      edges := {
        toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
        right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
      internal_label v := by rcases v with v | ⟨a,v⟩; rfl; cases a <;> rfl
      edge_label x := by rcases x with ⟨a,f⟩; cases a <;> rfl
      source x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.source f).map _).map _ = (G.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.source f).map _).map _ = (H.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
      target x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.target f).map _).map _ = (G.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.target f).map _).map _ = (H.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
    }

noncomputable def serial {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) :
    DeepIso (raise d (Serial.net G H)) (Serial.net (raise d G) (raise d H)) := by
  simpa only [graph_eq_raise] using DeepIso.ofIso (serial_graph G H)
/-- Uniform relabelling commutes literally with the ordered parallel constructor. -/
theorem parallel_graph {d X} {I O : X → List Wire} {J K}
    (F : ∀ x, Hypernet d (I x) (O x)) (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration X) :
    graph (Net.Parallel.net F B finite) = Net.Parallel.net (fun x => graph (F x)) B finite := by
  unfold graph Net.relabel Net.Parallel.net
  congr 1
  all_goals funext e; apply List.map_congr_left; intro v _; cases v <;> rfl

/-- Padding preserves every component and the chosen ordered boundary. -/
theorem parallel {d X} {I O : X → List Wire} {J K}
    (F : ∀ x, Hypernet d (I x) (O x)) (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration X) :
    raise d (Net.Parallel.net F B finite) = Net.Parallel.net (fun x => raise d (F x)) B finite := by
  simpa only [graph_eq_raise] using parallel_graph F B finite

/-- Tensor assembly is the fixed concatenating instance of ordered parallel. -/
theorem tensor {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K) :
    raise d (Net.Tensor.net G H) = Net.Tensor.net (raise d G) (raise d H) := by
  unfold Net.Tensor.net
  rw [parallel]
  congr 1
  funext b
  cases b <;> rfl

/-- Padding respects interface equality casts. -/
theorem castInterfaces {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet d I O) :
    raise d (Translation.castInterfaces hi ho G) = Translation.castInterfaces hi ho (raise d G) := by
  cases hi; cases ho; rfl

/-- A primitive corolla at the next allowance has the same primitive and wiring. -/
theorem primitive (d : Nat) (p : Primitive) :
    raise d (primitiveNet d p) = primitiveNet (d+1) p := by cases d <;> rfl

/-- Distributor forests retain every contraction and weakening occurrence. -/
theorem distributor (s : ShareSort) (k m d : Nat) :
    raise d (Distributor.atDepth s k m d) = Distributor.atDepth s k m (d+1) := by
  cases d <;> rfl

/-- Variable and atom distributor ordering is unaffected by padding. -/
theorem environmentDistributor (d k h m : Nat) :
    raise d (Translation.environmentDistributor d k h m) =
      Translation.environmentDistributor (d+1) k h m := by
  unfold Translation.environmentDistributor
  rw [tensor,distributor,distributor]

theorem singleUse (d k h : Nat) :
    raise d (Translation.singleUse d k h) = Translation.singleUse (d+1) k h := by
  unfold Translation.singleUse
  rw [castInterfaces,environmentDistributor]

/-- Boxes preserve their metadata while their bodies are raised once. -/
theorem box {d bound k h} (G : Hypernet d [.term] (environmentInterface (bound+k) h)) :
    raise (d+1) (Copying.box G) = Copying.box (raise d G) := rfl

/-- The original lambda-box interface convention is retained. -/
theorem lambdaBox {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    raise (d+1) (Translation.lambdaBox G) = Translation.lambdaBox (raise d G) := by
  unfold Translation.lambdaBox
  rw [box,castInterfaces]
/-- The prescribed variable/atom exchange in pairs is independent of allowance. -/
theorem pair {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) :
    raise d (Translation.pair G H) = Translation.pair (raise d G) (raise d H) := by
  unfold Translation.pair
  rw [castInterfaces,parallel]
  congr 2
  funext b
  cases b <;> rfl

noncomputable def unary {d k h} (o : Unary) (G : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (Translation.unary o G)) (Translation.unary o (raise d G)) := by
  unfold Translation.unary
  have f := (serial (Serial.net (primitiveNet d (.operation (.unary o))) G)
    (Translation.singleUse d k h)).trans
    (Serial.congr (serial (primitiveNet d (.operation (.unary o))) G) (DeepIso.refl _))
  simpa only [primitive,singleUse] using f

noncomputable def abstraction {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    DeepIso (raise (d+1) (Translation.abstraction G)) (Translation.abstraction (raise d G)) := by
  unfold Translation.abstraction
  have f := (serial (Serial.net (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox G))
    (Translation.singleUse (d+1) k h)).trans
    (Serial.congr (serial (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox G)) (DeepIso.refl _))
  simpa only [primitive,singleUse,lambdaBox] using f

noncomputable def application {d k h} (G H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (Translation.application G H)) (Translation.application (raise d G) (raise d H)) := by
  unfold Translation.application
  have f := (serial (Serial.net (primitiveNet d (.operation .app)) (Translation.pair G H))
    (Translation.environmentDistributor d k h 2)).trans
    (Serial.congr (serial (primitiveNet d (.operation .app)) (Translation.pair G H)) (DeepIso.refl _))
  simpa only [primitive,environmentDistributor,pair] using f

noncomputable def binary {d k h} (o : Binary) (G H : Hypernet d [.term] (environmentInterface k h)) :
    DeepIso (raise d (Translation.binary o G H)) (Translation.binary o (raise d G) (raise d H)) := by
  unfold Translation.binary
  have f := (serial (Serial.net (primitiveNet d (.operation (.binary o))) (Translation.pair G H))
    (Translation.environmentDistributor d k h 2)).trans
    (Serial.congr (serial (primitiveNet d (.operation (.binary o))) (Translation.pair G H)) (DeepIso.refl _))
  simpa only [primitive,environmentDistributor,pair] using f
end Hypernets.Copying.Padding


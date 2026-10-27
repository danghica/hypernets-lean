import Hypernets.Copying.ApplicationMatch

/-! The literal beta reduct realizes the retained host and opened body presentation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph

def localMatch {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Match (before B G) (.input 0) B where
  app := head B G
  lam := lambdaEdge B G
  boxEdge := ⟨true,⟨false,⟨true,(0 : Fin 1)⟩⟩⟩
  functionWire := .inl (0 : Fin 2)
  thunkWire := .inr ⟨true,⟨false,.inl (0 : Fin 1)⟩⟩
  argumentPort := argument B G 1
  head_at := ⟨rfl,List.mem_cons_self⟩
  app_target := rfl
  lambda_label := rfl
  lambda_source := rfl
  lambda_target := rfl
  box_label := labelEquiv_refl _ _
  box_source := rfl

/-- Identify retained and exposed internal vertices by their original occurrences. -/
def openingVertices {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    (after B G).Internal → (localMatch B G).presentation.Vertex := by
  cases d
  all_goals
    exact fun
      | .inl _ => .inl (.inl (1 : Fin 2))
      | .inr ⟨false,x⟩ => .inr x
      | .inr ⟨true,x⟩ => .inl (.inr ⟨true,⟨true,x⟩⟩)

def openingEdges {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    (after B G).Edge → (localMatch B G).presentation.Edge := by
  cases d
  all_goals exact fun
    | ⟨false,e⟩ => .inr e
    | ⟨true,e⟩ => .inl ⟨true,⟨true,e⟩⟩

theorem opening_vertices_injective {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Function.Injective (openingVertices B G) := by
  cases d
  all_goals
    rintro (i | ⟨b,x⟩) (j | ⟨c,y⟩) eq
    · cases DiscardResult.fin_one i; cases DiscardResult.fin_one j; rfl
    · cases c <;> cases eq
    · cases b <;> cases eq
    · cases b <;> cases c <;> change _ = _ at eq
      · have same := Sum.inr.inj eq
        cases same; rfl
      · cases eq
      · cases eq
      · have eq := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (Sum.inr.inj (Sum.inl.inj eq))).2)).2
        cases eq; rfl

theorem opening_edges_injective {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Function.Injective (openingEdges B G) := by
  cases d
  all_goals
    rintro ⟨b,x⟩ ⟨c,y⟩ eq
    cases b <;> cases c <;> change _ = _ at eq
    · exact congrArg (Sigma.mk false) (Sum.inr.inj eq)
    · cases eq
    · cases eq
    · have eq := eq_of_heq (Sigma.mk.inj (eq_of_heq (Sigma.mk.inj (Sum.inl.inj eq)).2)).2
      cases eq; rfl

theorem opening_vertex_range {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (x : (localMatch B G).presentation.Vertex) :
    (∃ y, openingVertices B G y = x) ↔ (localMatch B G).presentation.keepVertex x := by
  cases d
  all_goals
    constructor
    · rintro ⟨y,rfl⟩
      rcases y with i | ⟨b,y⟩
      · exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
      · cases b
        · trivial
        · exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
    · cases x with
      | inr x => exact fun _ => ⟨.inr ⟨false,x⟩,rfl⟩
      | inl x =>
        rcases x with i | ⟨b,x⟩
        · intro h
          rcases Arithmetic.fin_two i with rfl | rfl
          · exact False.elim (h.1 rfl)
          · exact ⟨.inl (0 : Fin 1),rfl⟩
        · cases b with
          | false => exact nomatch x
          | true =>
            rcases x with ⟨b,x⟩
            cases b with
            | true => exact fun _ => ⟨.inr ⟨true,x⟩,rfl⟩
            | false =>
              rcases x with i | ⟨b,x⟩
              · cases DiscardResult.fin_one i
                exact fun h => False.elim (h.2 rfl)
              · cases b <;> exact nomatch x

theorem opening_edge_range {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (e : (localMatch B G).presentation.Edge) :
    (∃ f, openingEdges B G f = e) ↔ (localMatch B G).presentation.keepEdge e := by
  cases d
  all_goals
    constructor
    · rintro ⟨⟨b,e⟩,rfl⟩
      cases b
      · trivial
      · exact ⟨(by intro eq; cases eq),(by intro eq; cases eq),(by intro eq; cases eq)⟩
    · cases e with
      | inr e => exact fun _ => ⟨⟨false,e⟩,rfl⟩
      | inl e =>
        rcases e with ⟨b,e⟩
        cases b with
        | false => cases DiscardResult.fin_one e; exact fun h => False.elim (h.1 rfl)
        | true =>
          rcases e with ⟨b,e⟩
          cases b with
          | true => exact fun _ => ⟨⟨true,e⟩,rfl⟩
          | false =>
            rcases e with ⟨b,e⟩
            cases b <;> cases DiscardResult.fin_one e
            · exact fun h => False.elim (h.2.1 rfl)
            · exact fun h => False.elim (h.2.2 rfl)


/-- A right serial component retains every external output position. -/
theorem right_serial_output {d I J O} (A : Hypernet d I J) (C : Hypernet d J O) (i : Fin O.length) :
    BoundarySerial.rightInsert A C (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort true i) = _
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map]
    exact congrArg Port.output (Fin.ext rfl)

/-- The box keeps every free output in its original ordered boundary block. -/
theorem local_box_targets {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    (before B G).target (localMatch B G).boxEdge = freePorts (environmentInterface k h) O := by
  change ((((List.finRange (environmentInterface k h).length).map Port.output).map
    (BoundarySerial.rightInsert (primitiveNet (d+1) (.operation .lam)) (Translation.lambdaBox B))).map
    (Net.Parallel.embed (Net.Tensor.family (closure B) G)
      (Net.Tensor.boundary [.term] (environmentInterface k h) [.term] O) false) |>.map
      (BoundarySerial.rightInsert (primitiveNet (d+1) (.operation .app)) (Net.Tensor.net (closure B) G))) = _
  simp only [List.map_map,freePorts]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply,right_serial_output,Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join]
  exact right_serial_output _ _ _

/-- The exposed body uses the original request and bound-argument attachment. -/
theorem opening_body_port {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (v : (openBody B).Vertex) :
    Port.map (openingVertices B G) (bodyVertex (openBody B) G v) = (localMatch B G).bodyPort v := by
  cases v with
  | internal x => cases d <;> rfl
  | input i => cases DiscardResult.fin_one i; cases d <;> rfl
  | output i =>
    unfold Match.bodyPort
    simp only [local_box_targets]
    cases i using Fin.cases with
    | zero => cases d <;> rfl
    | succ i =>
      rw [free_outputs]
      simp [freePorts,freePort,Port.map]

/-- Retained argument ports keep their original source occurrence. -/
theorem opening_argument_port {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (v : G.Vertex) :
    Port.map (openingVertices B G) (argumentVertex (openBody B) G v) =
      Port.map Sum.inl (BoundarySerial.rightInsert (primitiveNet (d+1) (.operation .app))
        (Net.Tensor.net (closure B) G)
        (Net.Parallel.embed (Net.Tensor.family (closure B) G)
          (Net.Tensor.boundary [.term] (environmentInterface k h) [.term] O) true v)) := by
  cases v with
  | internal x => cases d <;> rfl
  | input i =>
    cases DiscardResult.fin_one i
    cases d <;> rfl
  | output i =>
    rw [argument_outputs]
    change (Port.output (⟨(environmentInterface k h).length+i.val,by simp⟩ : Fin _)) =
      Port.map Sum.inl (BoundarySerial.rightInsert _ _ (.output _))
    rw [right_serial_output]
    rfl

/-- The literal beta successor realizes every retained and exposed occurrence. -/
def opening_realization {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) : Opening.Realization (localMatch B G).presentation (after B G) where
  vertices := openingVertices B G
  edges := openingEdges B G
  vertex_injective := opening_vertices_injective B G
  edge_injective := opening_edges_injective B G
  vertex_range := opening_vertex_range B G
  edge_range := opening_edge_range B G
  internal_label := by
    rintro (i | ⟨b,x⟩)
    · cases d <;> rfl
    · cases b <;> cases d <;> rfl
  edge_label := by
    rintro ⟨b,e⟩
    cases b <;> cases d <;> exact labelEquiv_refl _ _
  source := by
    cases d
    all_goals
     rintro ⟨b,e⟩
     cases b with
     | false =>
       change (((openBody B).source e).map (bodyVertex (openBody B) G)).map _ = _
       rw [List.map_map]
       exact List.map_congr_left (fun v _ => opening_body_port B G v)
     | true =>
       change ((G.source e).map (argumentVertex (openBody B) G)).map _ = _
       rw [List.map_map]
       change _ = ((((G.source e).map _).map _).map _)
       rw [List.map_map,List.map_map]
       exact List.map_congr_left (fun v _ => opening_argument_port B G v)
  target := by
    cases d
    all_goals
     rintro ⟨b,e⟩
     cases b with
     | false =>
       change (((openBody B).target e).map (bodyVertex (openBody B) G)).map _ = _
       rw [List.map_map]
       exact List.map_congr_left (fun v _ => opening_body_port B G v)
     | true =>
       change ((G.target e).map (argumentVertex (openBody B) G)).map _ = _
       rw [List.map_map]
       change _ = ((((G.target e).map _).map _).map _)
       rw [List.map_map,List.map_map]
       exact List.map_congr_left (fun v _ => opening_argument_port B G v)
end Hypernets.Copying.Application

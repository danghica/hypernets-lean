import Hypernets.Copying.TemplateInputSafety

/-! Free-interface permutations commute with micro-beta's literal bound-output splice. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace TypedPermutation

def blocks {F O : List Wire} (p : TypedPermutation F) (q : TypedPermutation O) :
    Bijection (Σ b, Fin (Net.Tensor.interfaces F O b).length) (Σ b, Fin (Net.Tensor.interfaces F O b).length) where
  toFun | ⟨false,i⟩ => ⟨false,p.bijection.toFun i⟩ | ⟨true,i⟩ => ⟨true,q.bijection.toFun i⟩
  invFun | ⟨false,i⟩ => ⟨false,p.bijection.invFun i⟩ | ⟨true,i⟩ => ⟨true,q.bijection.invFun i⟩
  left_inv x := by rcases x with ⟨b,i⟩; cases b <;> simp [p.bijection.left_inv,q.bijection.left_inv]
  right_inv x := by rcases x with ⟨b,i⟩; cases b <;> simp [p.bijection.right_inv,q.bijection.right_inv]

/-- Independent typed actions on two concatenated output blocks. -/
def append {F O : List Wire} (p : TypedPermutation F) (q : TypedPermutation O) : TypedPermutation (F++O) where
  bijection := (Net.Tensor.ports F O).symm.trans ((blocks p q).trans (Net.Tensor.ports F O))
  typed i := by
    have hi := Net.Tensor.join_split F O i
    generalize he : Net.Tensor.split F O i = x at hi
    rcases x with ⟨b,j⟩
    rw [← hi]
    cases b <;> simp [Bijection.trans,Bijection.symm,blocks,Net.Tensor.ports,
      Net.Tensor.split_join,Net.Tensor.join_label,Net.Tensor.interfaces,p.typed,q.typed]

@[simp] theorem append_left {F O : List Wire} (p : TypedPermutation F) (q : TypedPermutation O) (i : Fin F.length) :
    (p.append q).bijection.toFun (Net.Tensor.join F O ⟨false,i⟩) = Net.Tensor.join F O ⟨false,p.bijection.toFun i⟩ := by
  simp [append,Bijection.trans,Bijection.symm,blocks,Net.Tensor.ports,Net.Tensor.split_join]
@[simp] theorem append_right {F O : List Wire} (p : TypedPermutation F) (q : TypedPermutation O) (i : Fin O.length) :
    (p.append q).bijection.toFun (Net.Tensor.join F O ⟨true,i⟩) = Net.Tensor.join F O ⟨true,q.bijection.toFun i⟩ := by
  simp [append,Bijection.trans,Bijection.symm,blocks,Net.Tensor.ports,Net.Tensor.split_join]
end TypedPermutation

namespace Application.SpliceBoundary
variable {d : Nat} {F O : List Wire}

def bodyInsert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) : B.Vertex → (splice B G).Vertex := by
  cases d
  all_goals exact fun
    | .input i => .input i
    | .internal v => .internal (.inr ⟨false,v⟩)
    | .output i => Fin.cases (.internal (.inl (0 : Fin 1))) (fun j => freePort F O j) i

def argumentInsert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) : G.Vertex → (splice B G).Vertex := by
  cases d
  all_goals exact fun
    | .input i => .internal (.inl i)
    | .internal v => .internal (.inr ⟨true,v⟩)
    | .output i => valuePort F O i

def rawBodyInsert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) : B.Vertex → (splice B G).Vertex := by
  cases d
  all_goals exact Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) false

def rawArgumentInsert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) : G.Vertex → (splice B G).Vertex := by
  cases d
  all_goals exact Net.Expansion.insert (splicePattern _ F O) (spliceFilling B G) true

theorem body_insert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) (v : B.Vertex) :
    rawBodyInsert B G v = bodyInsert B G v := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    have eq : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
    subst i; rfl
  | output i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · change Port.map Sum.inl ((splicePattern 0 F O).targetPort false j.succ) = freePort F O j
      simp [Net.targetPort,splicePattern,spliceFrame,spliceTarget,freePorts,Net.relabel,
        List.getElem_map,List.getElem_finRange,freePort,Port.map]

theorem argument_insert (B : Hypernet d [.term] (.term :: F)) (G : Hypernet d [.term] O) (v : G.Vertex) :
    rawArgumentInsert B G v = argumentInsert B G v := by
  cases d <;> cases v with
  | internal v => rfl
  | input i =>
    have eq : i = (0 : Fin 1) := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
    subst i; rfl
  | output i =>
    change Port.map Sum.inl ((splicePattern 0 F O).targetPort true i) = valuePort F O i
    simp [Net.targetPort,splicePattern,spliceFrame,spliceTarget,valuePorts,Net.relabel,
      List.getElem_map,List.getElem_finRange,valuePort,Port.map]

variable {B C : Hypernet d [.term] (.term :: F)}
    (f : BoundaryIso B C) (p : TypedPermutation F) (G : Hypernet d [.term] O)

def ports : Bijection (splice B G).Vertex (splice C G).Vertex := by
  cases d
  all_goals exact {
    toFun := fun
      | .input i => .input i
      | .output i => .output ((p.append (.refl O)).bijection.toFun i)
      | .internal (.inl j) => .internal (.inl j)
      | .internal (.inr ⟨false,v⟩) => .internal (.inr ⟨false,f.internals.toFun v⟩)
      | .internal (.inr ⟨true,v⟩) => .internal (.inr ⟨true,v⟩)
    invFun := fun
      | .input i => .input i
      | .output i => .output ((p.append (.refl O)).bijection.invFun i)
      | .internal (.inl j) => .internal (.inl j)
      | .internal (.inr ⟨false,v⟩) => .internal (.inr ⟨false,f.internals.invFun v⟩)
      | .internal (.inr ⟨true,v⟩) => .internal (.inr ⟨true,v⟩)
    left_inv := by
      rintro (v | i | i)
      · rcases v with j | ⟨b,v⟩; rfl; cases b; simp [f.internals.left_inv]; rfl
      · rfl
      · simp [(p.append (.refl O)).bijection.left_inv]
    right_inv := by
      rintro (v | i | i)
      · rcases v with j | ⟨b,v⟩; rfl; cases b; simp [f.internals.right_inv]; rfl
      · rfl
      · simp [(p.append (.refl O)).bijection.right_inv] }

/-- The body action fixes the bound output zero and permutes only its free tail. -/
def Action : Prop := ∀ i, f.outputs.toFun i = (p.extend 1).bijection.toFun i

theorem body_commutes (action : Action f p) (v : B.Vertex) :
    (ports f p G).toFun (bodyInsert B G v) = bodyInsert C G (f.ports.toFun v) := by
  cases v with
  | internal v => rw [f.map_internal]; cases d <;> rfl
  | input i =>
    rw [f.map_input]
    have eq : f.inputMap i = i := f.input_singleton i
    rw [eq]
    cases d <;> rfl
  | output i =>
    rw [f.map_output]
    change _ = bodyInsert C G (.output (f.outputs.toFun i))
    rw [action i]
    refine Fin.cases ?_ (fun j => ?_) i
    · cases d <;> rfl
    · have eq : (p.extend 1).bijection.toFun j.succ = (p.bijection.toFun j).succ := by
        apply Fin.ext
        simp [TypedPermutation.extend,TypedPermutation.prefixMap,show ¬ j.val+1 < 1 by omega,Nat.add_comm]
      rw [eq]
      cases d
      all_goals
        change Port.output ((p.append (.refl O)).bijection.toFun (Net.Tensor.join F O ⟨false,j⟩)) =
          Port.output (Net.Tensor.join F O ⟨false,p.bijection.toFun j⟩)
        rw [TypedPermutation.append_left]

theorem argument_commutes (v : G.Vertex) :
    (ports f p G).toFun (argumentInsert B G v) = argumentInsert C G v := by
  cases d <;> cases v with
  | internal v => rfl
  | input i => rfl
  | output i =>
    change Port.output ((p.append (.refl O)).bijection.toFun (Net.Tensor.join F O ⟨true,i⟩)) =
      Port.output (Net.Tensor.join F O ⟨true,i⟩)
    rw [TypedPermutation.append_right]; rfl

def edges : Bijection (splice B G).Edge (splice C G).Edge := by
  cases d
  all_goals exact {
    toFun := fun | ⟨false,e⟩ => ⟨false,f.edges.toFun e⟩ | ⟨true,e⟩ => ⟨true,e⟩
    invFun := fun | ⟨false,e⟩ => ⟨false,f.edges.invFun e⟩ | ⟨true,e⟩ => ⟨true,e⟩
    left_inv := by rintro ⟨b,e⟩; cases b; simp [f.edges.left_inv]; rfl
    right_inv := by rintro ⟨b,e⟩; cases b; simp [f.edges.right_inv]; rfl }

/-- Literal splicing is natural for exactly the bound-fixing free action. -/
def iso (action : Action f p) : BoundaryIso (splice B G) (splice C G) where
  ports := ports f p G
  edges := edges f G
  vertex_label v := by
    cases d <;> rcases v with v | i | i
    all_goals first
      | rfl
      | exact (p.append (.refl O)).typed i
      | (rcases v with j | ⟨b,v⟩; rfl; cases b; exact f.internal_label v; rfl)
  input_iff v := by cases d <;> rcases v with v | i | i; all_goals first | rfl | (rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl)
  output_iff v := by cases d <;> rcases v with v | i | i; all_goals first | rfl | (rcases v with j | ⟨b,v⟩; rfl; cases b <;> rfl)
  edge_label e := by cases d <;> rcases e with ⟨b,e⟩ <;> cases b; all_goals first | exact f.edge_label e | exact labelEquiv_refl _ _
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (change ((B.source e).map _).map _ = (C.source (f.edges.toFun e)).map _
         rw [← f.source e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => by
           change (ports f p G).toFun (rawBodyInsert B G v) = rawBodyInsert C G (f.ports.toFun v)
           rw [body_insert,body_insert]
           exact body_commutes f p G action v))
      | (change ((G.source e).map _).map _ = (G.source e).map _
         rw [List.map_map]
         exact List.map_congr_left (fun v _ => by
           change (ports f p G).toFun (rawArgumentInsert B G v) = rawArgumentInsert C G v
           rw [argument_insert,argument_insert]
           exact argument_commutes f p G v))
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (change ((B.target e).map _).map _ = (C.target (f.edges.toFun e)).map _
         rw [← f.target e,List.map_map,List.map_map]
         exact List.map_congr_left (fun v _ => by
           change (ports f p G).toFun (rawBodyInsert B G v) = rawBodyInsert C G (f.ports.toFun v)
           rw [body_insert,body_insert]
           exact body_commutes f p G action v))
      | (change ((G.target e).map _).map _ = (G.target e).map _
         rw [List.map_map]
         exact List.map_congr_left (fun v _ => by
           change (ports f p G).toFun (rawArgumentInsert B G v) = rawArgumentInsert C G v
           rw [argument_insert,argument_insert]
           exact argument_commutes f p G v))

/-- Compensating the free action restores a boundary-fixing recursive isomorphism. -/
def compensate (action : Action f p) :
    DeepIso (splice B G) (InterfacePermutation.net (splice C G) (p.append (.refl O)).symm) :=
  InterfacePermutation.compensate (iso f p G action) _ (fun i => (iso f p G action).input_singleton i)
    (by intro i; apply Port.output.inj (Internal := (splice C G).Internal) (inputs := 1)
        change Port.output ((iso f p G action).outputMap i) = _
        rw [← BoundaryIso.map_output]; cases d <;> rfl)
end Application.SpliceBoundary
end Hypernets.Copying

import Hypernets.Copying.RetainedFrameTransfer
import Hypernets.Copying.BindingFillingBoxes

/-! Edge witnesses retain the literal original corolla as their common
context, including its hole name and its original recursive box body. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace CorollaExpansion
variable {d} (a : (alphabet d).Symbol)
    (G : Hypernet d ((alphabet d).signature.input a) ((alphabet d).signature.output a))

def vertices : Bijection ((Net.corolla (alphabet d).signature a).expand (fun _ => G)).Internal G.Internal where
  toFun | .inl x => nomatch x | .inr ⟨_,v⟩ => v
  invFun v := .inr ⟨0,v⟩
  left_inv v := by
    rcases v with v | ⟨e,v⟩
    · exact nomatch v
    · have eq : e = (0 : Fin 1) := Fin.ext (by omega)
      subst e; rfl
  right_inv _ := rfl

def edges : Bijection ((Net.corolla (alphabet d).signature a).expand (fun _ => G)).Edge G.Edge where
  toFun x := x.2
  invFun e := ⟨0,e⟩
  left_inv x := by
    obtain ⟨e,x⟩ := x
    have eq : e = (0 : Fin 1) := Fin.ext (by omega)
    subst e; rfl
  right_inv _ := rfl

theorem map_insert (e : Fin 1) (v : G.Vertex) :
    Port.map (vertices a G).toFun
      (Net.Expansion.insert (Net.corolla (alphabet d).signature a) (fun _ => G) e v) = v := by
  cases v with
  | internal v => rfl
  | input i => simp [Net.Expansion.insert,Net.sourcePort,Net.corolla,List.getElem_map,Net.Expansion.host,Port.map]
  | output i => simp [Net.Expansion.insert,Net.targetPort,Net.corolla,List.getElem_map,Net.Expansion.host,Port.map]

def iso : DeepIso ((Net.corolla (alphabet d).signature a).expand (fun _ => G)) G where
  vertices := vertices a G
  edges := edges a G
  internal_label v := by rcases v with v | ⟨e,v⟩; exact nomatch v; rfl
  edge_label _ := labelEquiv_refl d _
  source x := by
    change ((G.source x.2).map _).map _ = G.source x.2
    rw [List.map_map]
    calc
      _ = (G.source x.2).map id := List.map_congr_left (fun v _ => map_insert a G x.1 v)
      _ = _ := List.map_id _
  target x := by
    change ((G.target x.2).map _).map _ = G.target x.2
    rw [List.map_map]
    calc
      _ = (G.target x.2).map id := List.map_congr_left (fun v _ => map_insert a G x.1 v)
      _ = _ := List.map_id _
end CorollaExpansion

namespace FillingWitness
/-- The original edge context is used literally, rather than reconstructed
from an arbitrary representative of the two contributed graphs. -/
noncomputable def originalEdge {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) (free : FocusFree C) : FillingWitness T (L e) (R e) where
  context := Net.corolla (alphabet d).signature (C.edgeLabel e)
  free _ := free e
  left _ := L e
  right _ := R e
  edges _ := by
    cases cert with
    | retained l r => exact .retained l r
    | filled h label rel => exact .filled h label rel
    | boxed b label inner l r => exact .boxed b label inner l r
  leftIso := CorollaExpansion.iso _ _
  rightIso := CorollaExpansion.iso _ _

theorem originalEdge_context {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) (free : FocusFree C) :
    (originalEdge cert free).context = Net.corolla (alphabet d).signature (C.edgeLabel e) := rfl

/-- Restricting an edge certificate preserves its original context label and
all of its nested binding-free paths. -/
theorem originalEdge_binding {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e) (free : BindingFree C) :
    BindingFree (originalEdge cert free.1).context := by
  refine ⟨fun _ => free.1 e,?_⟩
  have shallow : ShallowBindingFree (Net.corolla (alphabet d).signature (C.edgeLabel e)) := by
    intro a b _ _ _ ⟨g,⟨v,tgt,src⟩,_⟩
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp tgt
    obtain ⟨j,_,eq⟩ := List.mem_map.mp src
    cases eq
  cases d with
  | zero => exact shallow
  | succ d => exact ⟨shallow,fun _ => free.2.2 e⟩
end FillingWitness
end Hypernets.Copying

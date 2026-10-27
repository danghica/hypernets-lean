import Hypernets.Copying.CopySuccessorMatch

/-! A source-relative presentation retains the entire old graph and adds the literal copy machinery. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening

/-- The original middle-block exchange, including its interface equality cast. -/
def copyOutput (k h : Nat) (side : Bool) (i : Fin (environmentInterface k h).length) :
    Fin (environmentInterface (k*2) (h*2)).length :=
  Fin.cast (congrArg List.length (by simp [environmentInterface,Nat.mul_two]))
    ((Translation.pairBoundary k h).outputs.toFun ⟨side,by cases side <;> exact i⟩)

abbrev AddedVertex {d k h} (H : Hypernet d [.term] (environmentInterface k h)) :=
  H.Internal ⊕ (Fin 1 ⊕ (Fin (environmentInterface (k*2) (h*2)).length ⊕ (Translation.environmentDistributor d k h 2).Internal))
abbrev AddedEdge {d k h} (H : Hypernet d [.term] (environmentInterface k h)) :=
  H.Edge ⊕ (Fin 1 ⊕ (Translation.environmentDistributor d k h 2).Edge)

namespace SuccessorMatch
variable {d I O k h} {G : Hypernet d I O} {v : G.Vertex}
  {H : Hypernet d [.term] (environmentInterface k h)} (a : SuccessorMatch G v H)

def weakPort : Port (G.Internal ⊕ AddedVertex H) I.length O.length := .internal (.inr (.inr (.inl 0)))
def linkPort (i : Fin (environmentInterface (k*2) (h*2)).length) : Port (G.Internal ⊕ AddedVertex H) I.length O.length :=
  .internal (.inr (.inr (.inr (.inl i))))

def copyPort : H.Vertex → Port (G.Internal ⊕ AddedVertex H) I.length O.length
  | .internal x => .internal (.inr (.inl x))
  | .input _ => Port.map Sum.inl v
  | .output i => linkPort (copyOutput k h false i)

def distributorPort : (Translation.environmentDistributor d k h 2).Vertex → Port (G.Internal ⊕ AddedVertex H) I.length O.length
  | .internal x => .internal (.inr (.inr (.inr (.inr x))))
  | .input i => linkPort i
  | .output i => Port.map Sum.inl ((G.target a.tail)[i.val]'(by rw [a.output_length];exact i.isLt))

@[reducible] noncomputable def presentation : Opening.Presentation d I O := by
  classical
  exact {
  Vertex := G.Internal ⊕ AddedVertex H
  Edge := G.Edge ⊕ AddedEdge H
  vertexLabel
    | .inl x => G.internalLabel x
    | .inr (.inl x) => H.internalLabel x
    | .inr (.inr (.inl _)) => .term
    | .inr (.inr (.inr (.inl i))) => (environmentInterface (k*2) (h*2))[i]
    | .inr (.inr (.inr (.inr x))) => (Translation.environmentDistributor d k h 2).internalLabel x
  edgeLabel
    | .inl e => G.edgeLabel e
    | .inr (.inl e) => H.edgeLabel e
    | .inr (.inr (.inl _)) => primitiveLabel d (.weakening .term)
    | .inr (.inr (.inr e)) => (Translation.environmentDistributor d k h 2).edgeLabel e
  keepVertex _ := True
  keepEdge _ := True
  source
    | .inl e => if e = a.active then selectedSources a.right weakPort (Port.map Sum.inl a.other)
        else (G.source e).map (Port.map Sum.inl)
    | .inr (.inl e) => (H.source e).map (copyPort (v := v))
    | .inr (.inr (.inl _)) => []
    | .inr (.inr (.inr e)) => ((Translation.environmentDistributor d k h 2).source e).map a.distributorPort
  target
    | .inl e => if e = a.tail then (List.finRange (environmentInterface k h).length).map (fun i => linkPort (copyOutput k h true i))
        else (G.target e).map (Port.map Sum.inl)
    | .inr (.inl e) => (H.target e).map (copyPort (v := v))
    | .inr (.inr (.inl _)) => [weakPort]
    | .inr (.inr (.inr e)) => ((Translation.environmentDistributor d k h 2).target e).map a.distributorPort
  }
end SuccessorMatch

structure SuccessorCertificate {d I O k h} (G K : Hypernet d I O) (v : G.Vertex) (w : K.Vertex)
    (H : Hypernet d [.term] (environmentInterface k h)) where
  matched : SuccessorMatch G v H
  realization : Opening.Realization matched.presentation K
  token : Port.map realization.vertices w = Port.map Sum.inl v
end Hypernets.Copying.CopyRule

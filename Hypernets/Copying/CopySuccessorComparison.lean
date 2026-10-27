import Hypernets.Copying.CopySuccessorPlug

/-! Comparing complete copying results across independent tree and payload matches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule.SuccessorMatch
open Graph Opening
variable {d I O k h} {G : Hypernet d I O} {v : G.Vertex}
    {H K : Hypernet d [.term] (environmentInterface k h)}

def addedVertices (f : DeepIso H K) : Bijection (AddedVertex H) (AddedVertex K) := f.vertices.sum (Bijection.refl _)
def addedEdges (f : DeepIso H K) : Bijection (AddedEdge H) (AddedEdge K) := f.edges.sum (Bijection.refl _)

theorem copyPort_congr (f : DeepIso H K) (p : H.Vertex) :
    Port.map ((Bijection.refl G.Internal).sum (addedVertices f)).toFun (copyPort (v := v) p) =
      copyPort (v := v) (Port.map f.vertices.toFun p) := by
  cases p with
  | internal x => rfl
  | input i => cases v <;> rfl
  | output i => rfl

theorem distributorPort_congr (a : SuccessorMatch G v H) (b : SuccessorMatch G v K)
    (f : DeepIso H K) (tails : a.tail = b.tail) (p : (Translation.environmentDistributor d k h 2).Vertex) :
    Port.map ((Bijection.refl G.Internal).sum (addedVertices f)).toFun (a.distributorPort p) = b.distributorPort p := by
  cases p with
  | internal x => rfl
  | input i => rfl
  | output i =>
    simp only [distributorPort,tails]
    cases (G.target b.tail)[i.val]'(by rw [b.output_length];exact i.isLt) <;> rfl

noncomputable def payloadPresentation (a : SuccessorMatch G v H) (b : SuccessorMatch G v K)
    (f : DeepIso H K) (tails : a.tail = b.tail) : a.presentation.Iso b.presentation where
  vertices := (Bijection.refl G.Internal).sum (addedVertices f)
  edges := (Bijection.refl G.Edge).sum (addedEdges f)
  vertex_range _ := Iff.rfl
  edge_range _ := Iff.rfl
  vertex_label := by
    rintro (x | (x | (x | (x | x))))
    · rfl
    · exact f.internal_label x
    · rfl
    · rfl
    · rfl
  edge_label := by
    rintro (e | (e | (e | e)))
    · exact labelEquiv_refl _ _
    · exact f.edge_label e
    · exact labelEquiv_refl _ _
    · exact labelEquiv_refl _ _
  source := by
    classical
    obtain ⟨activeEq,rightEq,otherEq⟩ := a.frame_unique b
    rintro (e | (e | (e | e)))
    · simp only [presentation,Bijection.sum,Bijection.refl,Sum.elim,Function.comp_apply,id_eq,activeEq,rightEq,otherEq]
      by_cases eq : e = b.active
      · simp only [ite_eq_left eq]
        cases hb : b.right <;> simp only [selectedSources,hb,Bool.false_eq_true,↓reduceIte,List.map_cons,List.map_nil]
        all_goals cases b.other <;> rfl
      · simp only [ite_eq_right eq,List.map_map]
        exact List.map_congr_left (fun p _ => by cases p <;> rfl)
    · change ((H.source e).map _).map _ = (K.source (f.edges.toFun e)).map _
      rw [← f.source,List.map_map,List.map_map]
      exact List.map_congr_left (fun p _ => copyPort_congr f p)
    · rfl
    · change (((Translation.environmentDistributor d k h 2).source e).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun p _ => distributorPort_congr a b f tails p)
  target := by
    classical
    rintro (e | (e | (e | e)))
    · simp only [presentation,Bijection.sum,Bijection.refl,Sum.elim,Function.comp_apply,id_eq,tails]
      by_cases eq : e = b.tail
      · simp only [ite_eq_left eq,List.map_map]; rfl
      · simp only [ite_eq_right eq,List.map_map]
        exact List.map_congr_left (fun p _ => by cases p <;> rfl)
    · change ((H.target e).map _).map _ = (K.target (f.edges.toFun e)).map _
      rw [← f.target,List.map_map,List.map_map]
      exact List.map_congr_left (fun p _ => copyPort_congr f p)
    · rfl
    · change (((Translation.environmentDistributor d k h 2).target e).map _).map _ = _
      rw [List.map_map]
      exact List.map_congr_left (fun p _ => distributorPort_congr a b f tails p)
end Hypernets.Copying.CopyRule.SuccessorMatch

namespace Hypernets.Copying.CopyRule.SuccessorCertificate
open Graph Opening

theorem coherent {d I O k h l j} {G R S : Hypernet d I O} {v w u}
    {H : Hypernet d [.term] (environmentInterface k h)} {K : Hypernet d [.term] (environmentInterface l j)}
    (a : SuccessorCertificate G R v w H) (b : SuccessorCertificate G S v u K) :
    Nonempty (Combined.StateIso ⟨R,(.search,w)⟩ ⟨S,(.search,u)⟩) := by
  obtain ⟨related,tails⟩ := a.matched.payload_unique b.matched
  cases related with
  | graphs f =>
    let transported := a.realization.transport (a.matched.payloadPresentation b.matched f tails)
    refine ⟨transported.stateIso b.realization ?_⟩
    change Port.map (((Bijection.refl G.Internal).sum (SuccessorMatch.addedVertices f)).toFun ∘ a.realization.vertices) w = _
    rw [Arithmetic.Reduction.port_comp,a.token,b.token]
    cases v <;> rfl
end Hypernets.Copying.CopyRule.SuccessorCertificate

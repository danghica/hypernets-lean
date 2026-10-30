import Hypernets.Copying.ParametricityGraphs
import Hypernets.Copying.MatchEmbedding

/-! Every input of Figure 20 reaches exactly a surface lambda head and
returns immediately. No execution is allowed to enter a private box merely
by probing its value at the original template boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity
open Graph MatchEmbedding

def LambdaInputs {d I O} (G : Hypernet d I O) : Prop :=
  ∀ i : Fin I.length, ∃ e, HeadAt G (.input i) e (.operation .lam)

theorem lambdaInputs_payload {d k h}
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) : LambdaInputs (lambdaPayload B) := by
  intro i
  have hi : i = 0 := Fin.ext (by have := i.isLt; change i.val < 1 at this; change i.val = 0; omega)
  subst i
  refine ⟨Serial.leftEdge _ _ (show (primitiveNet (d+1) (.operation .lam)).Edge from (0 : Fin 1)),rfl,?_⟩
  change (.input 0 : (lambdaPayload B).Vertex) ∈ [.input 0]
  exact List.mem_cons_self

/-- Retaining a serial suffix preserves every source lambda head, including
when its output is attached to the private sharing tree. -/
theorem LambdaInputs.serial {d I O J} {G : Hypernet d I O} (heads : LambdaInputs G)
    (H : Hypernet d O J) : LambdaInputs (Serial.net G H) := by
  intro i
  obtain ⟨e,h⟩ := heads i
  refine ⟨(MatchEmbedding.serialLeft G H).edges e,?_⟩
  have h := (MatchEmbedding.serialLeft G H).head h
  cases d
  all_goals
    change HeadAt (Serial.net G H) (Port.map Sum.inl ((Serial.pattern 0 I O J).sourcePort false i)) _ _ at h
    simpa [Net.sourcePort,Serial.pattern,List.getElem_map,Port.map] using h

/-- Ordered disjoint juxtaposition preserves the surface lambda-head
property at every actual input, without inserting forwarding edges. -/
theorem LambdaInputs.tensor {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (left : LambdaInputs G) (right : LambdaInputs H) : LambdaInputs (Net.Tensor.net G H) := by
  intro i
  by_cases before : i.val < I.length
  · obtain ⟨e,label,source⟩ := left ⟨i.val,before⟩
    refine ⟨⟨false,e⟩,label,?_⟩
    change Port.input i ∈ (G.source e).map _
    refine List.mem_map.mpr ⟨.input ⟨i.val,before⟩,source,?_⟩
    rfl
  · let j : Fin J.length := ⟨i.val-I.length,by have bound := i.isLt; simp at bound; omega⟩
    obtain ⟨e,label,source⟩ := right j
    refine ⟨⟨true,e⟩,label,?_⟩
    change Port.input i ∈ (H.source e).map _
    refine List.mem_map.mpr ⟨.input j,source,?_⟩
    apply congrArg Port.input
    apply Fin.ext
    dsimp [Net.Parallel.embed,Net.Tensor.boundary,Net.Tensor.ports,Net.Tensor.join,j]
    omega

/-- Equality transport changes no input coordinate or edge occurrence. -/
theorem LambdaInputs.reboundary {d I O J K} {G : Hypernet d I O} (heads : LambdaInputs G)
    (hi : I = J) (ho : O = K) : LambdaInputs (G.reboundary hi ho) := by
  cases hi; cases ho
  simpa only [Net.reboundary_refl] using heads

theorem copies_lambdaInputs {d k} (G : Hypernet d [.term] (List.replicate k .term))
    (heads : LambdaInputs G) (m : Nat) : LambdaInputs (copies G m) := by
  induction m with
  | zero => intro i; exact Fin.elim0 i
  | succ m ih => exact (heads.tensor ih).reboundary _ _

theorem left_lambdaInputs {m₁ m₂} (d : Nat) (C : ContractionTree .term (m₁+m₂)) :
    LambdaInputs (left d C) :=
  (((copies_lambdaInputs _ (lambdaInputs_payload _) m₁).tensor
      (copies_lambdaInputs _ (lambdaInputs_payload _) m₂)).reboundary _ _).serial _ |>.serial _

theorem right_lambdaInputs (d m₁ m₂ : Nat) : LambdaInputs (right d m₁ m₂) :=
  ((copies_lambdaInputs _ (lambdaInputs_payload _) m₁).tensor
      (copies_lambdaInputs _ (lambdaInputs_payload _) m₂)).reboundary _ _

/-- The original search transition immediately returns from every surface
lambda value; no callback or private-store action is executed at entry. -/
theorem LambdaInputs.returns {d I O} {G : Hypernet d I O} (heads : LambdaInputs G)
    (i : Fin I.length) : Search.Step G (.search,.input i) (.backtrack,.input i) := by
  obtain ⟨e,label,source⟩ := heads i
  exact .search e (.operation .lam) (.input i) (.backtrack,.input i) label source rfl

end Hypernets.Copying.Parametricity

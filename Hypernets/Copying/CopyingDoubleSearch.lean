import Hypernets.Copying.CopyingDoubleRewrite
import Hypernets.Copying.CopyingTemplateEntry

/-! Exact search requests at the non-distinguished inputs of the original
copying reduct. Search moves through genuine context attachment maps only. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

theorem Search.step_reboundary {d I O J K} {G : Hypernet d I O} {s t}
    (hi : I = J) (ho : O = K) (step : Search.Step G s t) :
    Search.Step (G.reboundary hi ho) (s.1,Port.cast hi ho s.2) (t.1,Port.cast hi ho t.2) := by
  cases hi; cases ho
  let f : DeepIso G (G.reboundary rfl rfl) := {
    vertices := Bijection.refl _, edges := Bijection.refl _
    internal_label := fun _ => rfl
    edge_label := fun e => labelEquiv_refl d (G.edgeLabel e)
    source := by intro e; simp [Net.reboundary,Bijection.refl]
    target := by intro e; simp [Net.reboundary,Bijection.refl] }
  have transported := (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f)).step step
  simpa only [Search.ofBoundaryIso,Search.Transport.positions,BoundaryIso.ofDeepIso,
    f,Bijection.refl,Port.bijection,Port.map_id_fun,id_eq,Port.cast_refl] using transported

namespace CopyingDouble
variable {d n k h : Nat} (H : Hypernet d [.term] (environmentInterface k h))

theorem copiesWith_request
    (A : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length)
    (step : Search.Step A (.search,.input i) (.rewrite,.input i)) :
    Search.Step (copiesWith H A)
      (.search,.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (.rewrite,.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  cases d
  all_goals
    have lifted := Search.plug_insert (retainedContext (n := n) H) (retainedHole (n := n) H) A step
    have mapped := (Search.ofBoundaryIso (BoundaryIso.ofDeepIso
      (by simpa only [Net.reboundary_refl] using retainedIso H A))).step lifted
    have changed := Search.step_reboundary (J := List.replicate (n+2) Wire.term)
      (K := environmentInterface (k*2) (h*2)) (by simp [List.replicate_succ])
      (by simp [environmentInterface,Nat.mul_two]) mapped
    simpa [Search.ofBoundaryIso,Search.Transport.positions,BoundaryIso.ofDeepIso,Port.bijection,
      copiesWith,ParallelPair.net,Nat.add_comm,Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,
      retainedContext,retainedHole,Net.Parallel.net,Net.Parallel.incidence,Net.Tensor.family,
      primitiveNet,Net.corolla,CopyRule.pairBoundary,Net.Parallel.embed,Net.Tensor.ports,
      Net.Tensor.join,List.getElem_map,List.getElem_finRange,Port.map,Port.cast]
      using changed

theorem afterWith_request
    (A : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h))
    (i : Fin (List.replicate (n+1) Wire.term).length)
    (step : Search.Step A (.search,.input i) (.rewrite,.input i)) :
    Search.Step (afterWith H A)
      (.search,.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩)
      (.rewrite,.input ⟨i.val+1,by have bound := i.isLt; simp only [List.length_replicate] at *; omega⟩) := by
  have inside := copiesWith_request H A i step
  cases d
  all_goals
    have outer := Search.expand_insert (Serial.pattern _ _ _ _)
      (Serial.filling (copiesWith H A) (Translation.environmentDistributor _ k h 2)) false inside
    simpa [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Serial.pattern,
      List.getElem_map,List.getElem_finRange,Port.map,afterWith,Serial.net] using outer

/-- Original input one requests and executes exactly one further original copy. -/
theorem second_entry (T : ContractionTree .term (n+2)) (copyable : Copyable H) :
    (Combined.machine d (List.replicate (n+2) .term) (environmentInterface k h)).Steps 2
      ⟨CopyRule.after T H,(.search,.input ⟨1,by simp⟩)⟩
      ⟨afterSecond T H,(.search,.input ⟨1,by simp⟩)⟩ :=
  .cons (.search _ (afterWith_request H _ ⟨0,by simp⟩
    (CopyingTemplate.requests_copy (CopyRule.residualTree T) H ⟨0,by simp⟩)))
    (.cons (.rewrite (second_rewrite H T copyable)) (.zero _))

end CopyingDouble
end Hypernets.Copying

import Hypernets.Copying.AssignmentEnabled
import Hypernets.Copying.OccurrenceTensorBoundary

/-! Original beta enabledness uses its actual application and complete
lambda payload, together with the rooted readiness of the argument. The
argument may be a lambda edge inside an arbitrary shallow template family. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph Opening Combined

/-- An original rooted application of the supplied complete lambda payload
has an actual original beta rewrite. The stable argument corolla is recovered
from the actual search history, without a footprint-retention assumption. -/
theorem rooted_payload_enabled {d I O k h}
    (C : Hypernet (d+1) I O) (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (app : Occurrence (primitiveNet (d+1) (.operation .app)) C)
    (closure : Occurrence (lambdaPayload B) C)
    (function : app.ports (.output (0 : Fin 2)) = closure.ports (.input 0))
    {i : Fin I.length}
    (rooted : Search.RootedFrom C i (.rewrite,app.ports (.input (0 : Fin 1)))) :
    ∃ H : Hypernet (d+1) I O, ∃ w,
      Rewrite C (app.ports (.input (0 : Fin 1))) H w := by
  have head : MatchEmbedding.HeadAt C (app.ports (.input (0 : Fin 1)))
      (app.edges (0 : Fin 1)) (.operation .app) :=
    app.matchEmbedding.head ⟨rfl,List.mem_cons_self⟩
  have selected : (C.target (app.edges (0 : Fin 1)))[1]? =
      some (app.ports (.output (1 : Fin 2))) := by
    rw [← app.target]
    rfl
  obtain ⟨K,V,argument,stable,argumentInput⟩ :=
    (Search.rooted_rewrite_arguments rooted head 1 (by decide) _ selected).occurrence
  have different : closure.ports (.input 0) ≠ argument.ports (.input 0) := by
    rw [← function,argumentInput]
    have distinct := C.target_nodup (app.edges (0 : Fin 1))
    rw [← app.target] at distinct
    change [app.ports (.output (0 : Fin 2)),app.ports (.output (1 : Fin 2))].Nodup at distinct
    simpa only [List.nodup_cons,List.mem_singleton,List.not_mem_nil,List.nodup_nil,
      not_false_eq_true,and_true] using distinct
  let apart := BoxPullWeakening.ReverseComponents.lambda_stable_disjoint closure argument stable different
  let args := BoxPullWeakening.ReverseComponents.tensorJoin closure argument apart
  have boundary : ∀ j : Fin 2, app.ports (.output j) = args.ports (.input j) := by
    intro j
    have cases : j=(0 : Fin 2) ∨ j=1 := by
      by_cases zero : j.val=0
      · exact .inl (Fin.ext zero)
      · exact .inr (Fin.ext (by have := j.isLt; omega))
    rcases cases with rfl | rfl
    · exact function.trans (Occurrence.tensorJoin_left closure argument apart (.input (0 : Fin 1))).symm
    · exact argumentInput.symm.trans (Occurrence.tensorJoin_right closure argument apart (.input (0 : Fin 1))).symm
  have disjoint : ∀ e a, app.edges e ≠ args.edges a := by
    intro e a eq
    have active := app.matchEmbedding.primitive e (.operation .app) rfl
    change C.edgeLabel (app.edges e) = primitiveLabel (d+1) (.operation .app) at active
    rcases a with ⟨side,a⟩
    cases side with
    | false =>
      rcases a with ⟨part,a⟩
      cases part with
      | false =>
        have label := closure.matchEmbedding.primitive ⟨false,a⟩ (.operation .lam) rfl
        change C.edgeLabel (closure.edges ⟨false,a⟩) = primitiveLabel (d+1) (.operation .lam) at label
        change app.edges e = closure.edges ⟨false,a⟩ at eq
        rw [eq,label] at active
        cases active
      | true =>
        have label := closure.label ⟨true,a⟩
        change app.edges e = closure.edges ⟨true,a⟩ at eq
        rw [← eq,active] at label
        exact label
    | true =>
      obtain ⟨p,label,passive⟩ := stable.labels a
      have label := argument.matchEmbedding.primitive a p label
      change C.edgeLabel (argument.edges a) = primitiveLabel (d+1) p at label
      change app.edges e = argument.edges a at eq
      rw [eq,label] at active
      have same := primitiveLabel_injective (d+1) active
      subst p
      simp [StablePrimitive,Operation.kind] at passive
  let joint := Occurrence.SerialJoin.occurrence app args boundary disjoint
  have actual := joint.local_rewrite (.beta B V stable)
  rw [Occurrence.SerialJoin.occurrence_input] at actual
  exact ⟨_,_,actual⟩

end Hypernets.Copying.Application

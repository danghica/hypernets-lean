import Hypernets.Copying.BoxPullContractionReverseLambda
import Hypernets.Copying.BoxPullWeakeningParallelJoin

/-! Converse beta enabledness uses the actual original left lambda interface
and the same stable argument. All attachments remain at selected original ports. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullContraction.ReverseBeta
open Graph Opening Search.Expansion

/-- An original right beta match at a common token has an actual original
left beta rewrite, including shallow box-contraction and arbitrary deep cases. -/
theorem beta_enabled {d I O} (C : Hypernet (d+1) I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e) (free : FocusFree C)
    (closed : HoleFree (C.expand R)) {k h J}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (A : Hypernet (d+1) [.term] J) (stable : Stable A)
    (f : Occurrence (Application.before B A) (C.expand R))
    {v : C.Vertex} (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    ∃ H : Hypernet (d+1) I O, ∃ w,
      Combined.Rewrite (C.expand L) (Net.Expansion.host C L v) H w := by
  let app := (BoxPullWeakening.ReverseComponents.serialLeft (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (lambdaPayload B) A)).comp f
  let args := (BoxPullWeakening.ReverseComponents.serialRight (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (lambdaPayload B) A)).comp f
  let closure := (BoxPullWeakening.ReverseComponents.tensorLeft (lambdaPayload B) A).comp args
  let argument := (BoxPullWeakening.ReverseComponents.tensorRight (lambdaPayload B) A).comp args
  have appInput : app.ports (.input (0 : Fin 1)) = Net.Expansion.host C R v := attached
  obtain ⟨app',ports⟩ := ReverseLambda.primitive_at_input C cert closed app
    (fun _ => ⟨.operation .app,rfl⟩) (fun _ => List.mem_cons_self) appInput
  let head : (primitiveNet (d+1) (.operation .app)).Edge := by change Fin 1; exact 0
  have source : Net.Expansion.host C R v ∈ (C.expand R).source (app.edges head) := by
    rw [← appInput]
    exact app.matchEmbedding.source_mem (by cases d <;> exact List.mem_cons_self)
  obtain ⟨retained⟩ := right_primitive_retained C cert source
    (app.matchEmbedding.primitive head (.operation .app) rfl) (fun h bad => by cases bad)
  have leftLink : app.ports (.output (0 : Fin 2)) = closure.ports (.input (0 : Fin 1)) := by rfl
  have rightLink : app.ports (.output (1 : Fin 2)) = argument.ports (.input (0 : Fin 1)) := by rfl
  have leftTarget : closure.ports (.input (0 : Fin 1)) ∈ (C.expand R).target (app.edges head) := by
    rw [← app.target head]
    change closure.ports (.input (0 : Fin 1)) ∈ [app.ports (.output (0 : Fin 2)),app.ports (.output (1 : Fin 2))]
    exact leftLink ▸ List.mem_cons_self
  have rightTarget : argument.ports (.input (0 : Fin 1)) ∈ (C.expand R).target (app.edges head) := by
    rw [← app.target head]
    change argument.ports (.input (0 : Fin 1)) ∈ [app.ports (.output (0 : Fin 2)),app.ports (.output (1 : Fin 2))]
    exact rightLink ▸ List.mem_cons_of_mem _ List.mem_cons_self
  obtain ⟨lv,leftHost⟩ := retained.target_origin leftTarget
  obtain ⟨rv,rightHost⟩ := retained.target_origin rightTarget
  obtain ⟨k',h',B',closure',closureInput⟩ := ReverseLambda.reflectLambda C cert free closed B closure leftHost.symm
  obtain ⟨argument',argumentPorts⟩ := ReverseLambda.primitive_at_input C cert closed argument
    (fun e => by obtain ⟨p,label,_⟩ := stable.labels e; exact ⟨p,label⟩)
    (Stable.input_source stable.labels) rightHost.symm
  have left : app'.ports (.output (0 : Fin 2)) = closure'.ports (.input 0) :=
    (ports (.output (0 : Fin 2)) lv (leftLink.trans leftHost.symm)).trans closureInput.symm
  have right : app'.ports (.output (1 : Fin 2)) = argument'.ports (.input 0) :=
    (ports (.output (1 : Fin 2)) rv (rightLink.trans rightHost.symm)).trans
      (argumentPorts (.input 0) rv rightHost.symm).symm
  have different : closure'.ports (.input 0) ≠ argument'.ports (.input 0) := by
    rw [← left,← right]
    have distinct := (C.expand L).target_nodup (app'.edges head)
    rw [← app'.target] at distinct
    change [app'.ports (.output (0 : Fin 2)),app'.ports (.output (1 : Fin 2))].Nodup at distinct
    simpa only [List.nodup_cons,List.mem_singleton,not_false_eq_true,List.not_mem_nil,List.nodup_nil,and_true] using distinct
  let apart := BoxPullWeakening.ReverseComponents.lambda_stable_disjoint closure' argument' stable different
  let args' := BoxPullWeakening.ReverseComponents.tensorJoin closure' argument' apart
  have boundary : ∀ i, app'.ports (.output i) = args'.ports (.input i) := by
    intro i
    change Fin 2 at i
    have range : i.val = 0 ∨ i.val = 1 := by have := i.isLt; omega
    rcases range with zero | one
    · have eq : i = (0 : Fin 2) := Fin.ext zero
      subst i
      exact left
    · have eq : i = (1 : Fin 2) := Fin.ext one
      subst i
      exact right
  have disjoint : ∀ e a, app'.edges e ≠ args'.edges a := by
    intro e a eq
    have hp := app'.matchEmbedding.primitive e (.operation .app) rfl
    change (C.expand L).edgeLabel (app'.edges e) = primitiveLabel (d+1) (.operation .app) at hp
    rcases a with ⟨side,a⟩
    cases side with
    | false =>
      rcases a with ⟨part,a⟩
      cases part with
      | false =>
        have lp := closure'.matchEmbedding.primitive ⟨false,a⟩ (.operation .lam) rfl
        change (C.expand L).edgeLabel (closure'.edges ⟨false,a⟩) = primitiveLabel (d+1) (.operation .lam) at lp
        change app'.edges e = closure'.edges ⟨false,a⟩ at eq
        rw [eq,lp] at hp
        cases hp
      | true =>
        have bp := closure'.label ⟨true,a⟩
        change app'.edges e = closure'.edges ⟨true,a⟩ at eq
        rw [← eq,hp] at bp
        exact bp
    | true =>
      obtain ⟨p,label,passive⟩ := stable.labels a
      have ap := argument'.matchEmbedding.primitive a p label
      change (C.expand L).edgeLabel (argument'.edges a) = primitiveLabel (d+1) p at ap
      change app'.edges e = argument'.edges a at eq
      rw [eq,ap] at hp
      have same := primitiveLabel_injective (d+1) hp
      subst p
      simp [StablePrimitive,Operation.kind] at passive
  let joint := Occurrence.SerialJoin.occurrence app' args' boundary disjoint
  have step := joint.local_rewrite (.beta B' A stable)
  have position : joint.ports (.input (0 : Fin 1)) = Net.Expansion.host C L v := by
    rw [Occurrence.SerialJoin.occurrence_input]
    exact ports (.input (0 : Fin 1)) v appInput
  rw [position] at step
  exact ⟨_,_,step⟩
end Hypernets.Copying.BoxPullContraction.ReverseBeta

import Hypernets.Copying.BoxPullWeakeningReverseCopyable
import Hypernets.Copying.BoxPullWeakeningParallelJoin

/-! Converse beta enabledness reconstructs the complete original lambda and
retains the actual stable argument. Free outputs may grow only as prescribed
by the original BPullW pair. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Opening
namespace ReverseComponents

noncomputable def tensorLeft {d I J K L} (A : Hypernet d I J) (B : Hypernet d K L) :
    Occurrence A (Net.Tensor.net A B) :=
  Occurrence.ParallelJoin.component (Net.Tensor.family A B) (Net.Tensor.boundary I J K L)
    ⟨[false,true],by intro b; cases b <;> simp⟩ false
noncomputable def tensorRight {d I J K L} (A : Hypernet d I J) (B : Hypernet d K L) :
    Occurrence B (Net.Tensor.net A B) :=
  Occurrence.ParallelJoin.component (Net.Tensor.family A B) (Net.Tensor.boundary I J K L)
    ⟨[false,true],by intro b; cases b <;> simp⟩ true

/-- The lambda and evaluated argument cannot share an edge when their incoming
term ports are the two distinct actual application outputs. -/
theorem lambda_stable_disjoint {d k h I O J}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    {A : Hypernet (d+1) [.term] J} {G : Hypernet (d+1) I O}
    (f : Occurrence (lambdaPayload B) G) (g : Occurrence A G) (stable : Stable A)
    (different : f.ports (.input 0) ≠ g.ports (.input 0)) :
    ∀ e a, f.edges e ≠ g.edges a := by
  rintro ⟨side,e⟩ a eq
  cases side with
  | false =>
    have src := f.source ⟨false,e⟩
    change [f.ports (.input 0)] = G.source (f.edges ⟨false,e⟩) at src
    have member := g.matchEmbedding.source_mem (Stable.input_source stable.labels a)
    change g.ports (.input 0) ∈ G.source (g.edges a) at member
    rw [← eq,← src] at member
    exact different (List.mem_singleton.mp member).symm
  | true =>
    obtain ⟨p,label,_⟩ := stable.labels a
    have prim := g.matchEmbedding.primitive a p label
    change G.edgeLabel (g.edges a) = primitiveLabel (d+1) p at prim
    have box := f.label ⟨true,e⟩
    rw [eq,prim] at box
    exact box

/-- Join two actual disjoint components with the literal ordered tensor boundary. -/
noncomputable def tensorJoin {d I J K L X Y} {A : Hypernet d I J} {B : Hypernet d K L}
    {G : Hypernet d X Y} (f : Occurrence A G) (g : Occurrence B G)
    (disjoint : ∀ e a, f.edges e ≠ g.edges a) : Occurrence (Net.Tensor.net A B) G := by
  let each : ∀ b, Occurrence (Net.Tensor.family A B b) G := fun b => by cases b; exact f; exact g
  exact Occurrence.ParallelJoin.occurrence (Net.Tensor.family A B) (Net.Tensor.boundary I J K L)
    ⟨[false,true],by intro b; cases b <;> simp⟩ each (by
      intro a b ne e x
      cases a <;> cases b
      · exact False.elim (ne rfl)
      · exact disjoint e x
      · exact fun eq => disjoint x e eq.symm
      · exact False.elim (ne rfl))
end ReverseComponents

namespace Decoration
variable {d I O} {G : Hypernet (d+1) I O} (D : Decoration G)

/-- Actual right beta enabledness reflects to an original left beta rewrite.
The actual stable argument and all original larger free-box outputs are kept. -/
theorem beta_enabled {k h J} (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (A : Hypernet (d+1) [.term] J) (stable : Stable A)
    (f : Occurrence (Application.before B A) D.graph) :
    ∃ H : Hypernet (d+1) I O, ∃ v,
      Combined.Rewrite G (D.project (f.ports (.input 0))) H v := by
  let app := (ReverseComponents.serialLeft (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (lambdaPayload B) A)).comp f
  let args := (ReverseComponents.serialRight (primitiveNet (d+1) (.operation .app))
    (Net.Tensor.net (lambdaPayload B) A)).comp f
  let closure := (ReverseComponents.tensorLeft (lambdaPayload B) A).comp args
  let argument := (ReverseComponents.tensorRight (lambdaPayload B) A).comp args
  let app' := D.reflectPrimitiveOccurrence app.matchEmbedding
    (ReverseComponents.primitive_nonweak (d+1) (.operation .app) (fun s eq => by cases eq))
  let argument' := D.reflectPrimitiveOccurrence argument.matchEmbedding (ReverseComponents.stable_nonweak stable)
  obtain ⟨k',h',C,closure',inputs⟩ := D.reflectLambda B closure
  have left : app'.ports (.output (0 : Fin 2)) = closure'.ports (.input 0) := by
    rw [inputs]
    rfl
  have right : app'.ports (.output (1 : Fin 2)) = argument'.ports (.input 0) := by rfl
  have different : closure'.ports (.input 0) ≠ argument'.ports (.input 0) := by
    rw [← left,← right]
    have distinct := G.target_nodup (app'.edges (0 : Fin 1))
    rw [← app'.target] at distinct
    change [app'.ports (.output (0 : Fin 2)),app'.ports (.output (1 : Fin 2))].Nodup at distinct
    simpa only [List.nodup_cons,List.mem_singleton,not_false_eq_true,List.not_mem_nil,List.nodup_nil,and_true] using distinct
  let apart := ReverseComponents.lambda_stable_disjoint closure' argument' stable different
  let args' := ReverseComponents.tensorJoin closure' argument' apart
  have boundary : ∀ i, app'.ports (.output i) = args'.ports (.input i) := by
    intro i
    have range : i.val = 0 ∨ i.val = 1 := by have := i.isLt; change i.val < 2 at this; omega
    rcases range with zero | one
    · have eq : i = (0 : Fin 2) := Fin.ext zero
      subst i
      exact left
    · have eq : i = (1 : Fin 2) := Fin.ext one
      subst i
      exact right
  have disjoint : ∀ e a, app'.edges e ≠ args'.edges a := by
    intro e a eq
    have head := app'.matchEmbedding.primitive e (.operation .app) rfl
    change G.edgeLabel (app'.edges e) = primitiveLabel (d+1) (.operation .app) at head
    rcases a with ⟨side,a⟩
    cases side with
    | false =>
      rcases a with ⟨part,a⟩
      cases part with
      | false =>
        have lam := closure'.matchEmbedding.primitive ⟨false,a⟩ (.operation .lam) rfl
        change G.edgeLabel (closure'.edges ⟨false,a⟩) = primitiveLabel (d+1) (.operation .lam) at lam
        change app'.edges e = closure'.edges ⟨false,a⟩ at eq
        rw [eq,lam] at head
        cases head
      | true =>
        have box := closure'.label ⟨true,a⟩
        change app'.edges e = closure'.edges ⟨true,a⟩ at eq
        rw [← eq,head] at box
        exact box
    | true =>
      obtain ⟨p,label,passive⟩ := stable.labels a
      have arg := argument'.matchEmbedding.primitive a p label
      change G.edgeLabel (argument'.edges a) = primitiveLabel (d+1) p at arg
      change app'.edges e = argument'.edges a at eq
      rw [eq,arg] at head
      have same := primitiveLabel_injective (d+1) head
      subst p
      simp [StablePrimitive,Operation.kind] at passive
  let joint := Occurrence.SerialJoin.occurrence app' args' boundary disjoint
  have step := joint.local_rewrite (.beta C A stable)
  have position : joint.ports (.input (0 : Fin 1)) = D.project (f.ports (.input 0)) := by
    rw [Occurrence.SerialJoin.occurrence_input]
    change D.project (f.ports (BoundarySerial.leftInsert _ _ (.input 0))) = _
    rw [Combined.left_input]
  rw [position] at step
  exact ⟨_,_,step⟩
end Decoration
end Hypernets.Copying.BoxPullWeakening

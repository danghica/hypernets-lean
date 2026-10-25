import Hypernets.Copying.AtomicBoundaryActions

/-! Bijective renaming of the original translation for every lambda-free term,
including arbitrary nesting and sharing through application and all binary operations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

inductive LambdaFree {k h} : Term k h → Prop where
  | var (i : Fin k) : LambdaFree (.var i)
  | atom (a : Fin h) : LambdaFree (.atom a)
  | constant (c : Constant) : LambdaFree (.const c)
  | unary (o : Unary) {t} : LambdaFree t → LambdaFree (.unary o t)
  | application {t u} : LambdaFree t → LambdaFree u → LambdaFree (.app t u)
  | binary (o : Binary) {t u} : LambdaFree t → LambdaFree u → LambdaFree (.binary o t u)

namespace LambdaFree

theorem rename {k h l j} {t : Term k h} (free : LambdaFree t) (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    LambdaFree (Term.rename ρ α t) := by
  induction free with
  | var i => exact .var _
  | atom a => exact .atom _
  | constant c => exact .constant _
  | unary o _ ih => exact .unary o ih
  | application _ _ ih ih' => exact .application ih ih'
  | binary o _ _ ih ih' => exact .binary o ih ih'

theorem depth_zero {k h} {t : Term k h} (free : LambdaFree t) : Translation.depth t = 0 := by
  induction free <;> simp_all [Translation.depth]

/-- The existing translated graph with its provably zero allowance exposed.
This is equality transport only: no new translation or graph simplification. -/
def graph {k h} {t : Term k h} (free : LambdaFree t) : Hypernet 0 [.term] (environmentInterface k h) :=
  Translation.castDepth free.depth_zero (Translation.term t)

theorem graph_unary {k h} {t : Term k h} (free : LambdaFree t) (o : Unary) :
    graph (.unary o free) = Translation.unary o (graph free) :=
  Translation.castDepth_unary free.depth_zero o (Translation.term t)

/-- The two pads at a zero common allowance are the original pad-to-self identities. -/
theorem application_zero {d e k h} (hd : d = 0) (he : e = 0)
    (G : Hypernet d [.term] (environmentInterface k h)) (H : Hypernet e [.term] (environmentInterface k h)) :
    Translation.castDepth (show max d e = 0 by omega)
      (Translation.application (Translation.padTo _ (Nat.le_max_left _ _) G) (Translation.padTo _ (Nat.le_max_right _ _) H)) =
      Translation.application (Translation.castDepth hd G) (Translation.castDepth he H) := by
  cases hd; cases he
  rfl

theorem binary_zero {d e k h} (hd : d = 0) (he : e = 0) (o : Binary)
    (G : Hypernet d [.term] (environmentInterface k h)) (H : Hypernet e [.term] (environmentInterface k h)) :
    Translation.castDepth (show max d e = 0 by omega)
      (Translation.binary o (Translation.padTo _ (Nat.le_max_left _ _) G) (Translation.padTo _ (Nat.le_max_right _ _) H)) =
      Translation.binary o (Translation.castDepth hd G) (Translation.castDepth he H) := by
  cases hd; cases he
  rfl

theorem graph_application {k h} {t u : Term k h} (ft : LambdaFree t) (fu : LambdaFree u) :
    graph (.application ft fu) = Translation.application (graph ft) (graph fu) :=
  application_zero ft.depth_zero fu.depth_zero _ _

theorem graph_binary {k h} {t u : Term k h} (ft : LambdaFree t) (fu : LambdaFree u) (o : Binary) :
    graph (.binary o ft fu) = Translation.binary o (graph ft) (graph fu) :=
  binary_zero ft.depth_zero fu.depth_zero o _ _

/-- Strong induction invariant: the constructed isomorphism realises the same
specified resource action at every leaf and constructor. -/
theorem rename_with_action {k h} {t : Term k h} (free : LambdaFree t)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    ∃ f : BoundaryIso (graph free) (graph (free.rename ρ.toFun α.toFun)), ResourceAction ρ α f := by
  induction free with
  | var i => exact ⟨Translation.variableTerm_rename 0 ρ α i,Translation.variableTerm_action 0 ρ α i⟩
  | atom a => exact ⟨Translation.atom_rename 0 ρ α a,Translation.atom_action 0 ρ α a⟩
  | constant c => exact ⟨Translation.constant_rename 0 ρ α c,Translation.constant_action 0 ρ α c⟩
  | @unary o t free ih =>
    obtain ⟨f,hf⟩ := ih
    change ∃ q : BoundaryIso (graph (.unary o free)) (graph (.unary o (free.rename ρ.toFun α.toFun))), ResourceAction ρ α q
    rw [graph_unary free o,graph_unary (free.rename ρ.toFun α.toFun) o]
    exact ⟨Translation.unary_boundaryIso o f,hf.unary o⟩
  | @application t u ft fu ih ih' =>
    obtain ⟨f,hf⟩ := ih
    obtain ⟨g,hg⟩ := ih'
    change ∃ q : BoundaryIso (graph (.application ft fu)) (graph (.application (ft.rename ρ.toFun α.toFun) (fu.rename ρ.toFun α.toFun))), ResourceAction ρ α q
    rw [graph_application ft fu,graph_application (ft.rename ρ.toFun α.toFun) (fu.rename ρ.toFun α.toFun)]
    exact ⟨Translation.application_boundaryIso f g (hf.agree hg),hf.application hg⟩
  | @binary o t u ft fu ih ih' =>
    obtain ⟨f,hf⟩ := ih
    obtain ⟨g,hg⟩ := ih'
    change ∃ q : BoundaryIso (graph (.binary o ft fu)) (graph (.binary o (ft.rename ρ.toFun α.toFun) (fu.rename ρ.toFun α.toFun))), ResourceAction ρ α q
    rw [graph_binary ft fu o,graph_binary (ft.rename ρ.toFun α.toFun) (fu.rename ρ.toFun α.toFun) o]
    exact ⟨Translation.binary_boundaryIso f g (hf.agree hg) o,hf.binary hg o⟩

/-- Remove auxiliary allowance equalities without changing the actual graphs. -/
def uncast {d e I O} {G : Hypernet d I O} {H : Hypernet e I O}
    (hd : d = 0) (he : e = 0) (eq : e = d)
    (f : BoundaryIso (Translation.castDepth hd G) (Translation.castDepth he H)) :
    BoundaryIso G (Translation.castDepth eq H) := by
  cases hd; cases he; exact f
end LambdaFree

namespace Translation
/-- Public endpoint on the original translation, for arbitrary finite scopes.
There is no operand-matching, machine, stability, or robustness premise. -/
theorem lambdaFree_rename {k h} (t : Term k h) (free : LambdaFree t)
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) :
    Nonempty (BoundaryIso (term t)
      (castDepth (depth_rename t ρ.toFun α.toFun) (term (Term.rename ρ.toFun α.toFun t)))) := by
  obtain ⟨f,_⟩ := free.rename_with_action ρ α
  exact ⟨LambdaFree.uncast free.depth_zero (free.rename ρ.toFun α.toFun).depth_zero (depth_rename t ρ.toFun α.toFun) f⟩
end Translation
end Hypernets.Copying

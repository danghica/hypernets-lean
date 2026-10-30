import Hypernets.Copying.SharingExecution
import Hypernets.Copying.BindingFillingPlug

/-! Pointed semantic corrections by completed sharing templates inside any
focus-free host. The actual internal host token and its root are preserved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingExecution
open Graph Combined

/-- A sharing correction can be used at any unchanged typed host position.
The supplied root is transported through original search; it is never inferred
from observational equivalence. -/
theorem plug_pointed_class_exact_equiv {T : PreTemplate} (trees : T.SharingTrees)
    (padding : T.PaddingClosed) {d} (C : Hypernet d [.term] []) (free : FocusFree C)
    (e : C.Edge) {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (left : HoleFree (C.plug e G)) (right : HoleFree (C.plug e H))
    (mode) (v : C.Vertex) (typed : C.vertexLabel v = .term) (nonrewrite : mode ≠ .rewrite)
    (rooted : StateClass.Rooted (StateClass.ofState ⟨d,C.plug e G,
      (mode,Net.Replacement.host C e G v)⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,C.plug e G,(mode,Net.Replacement.host C e G v)⟩)
      (StateClass.ofState ⟨d,C.plug e H,(mode,Net.Replacement.host C e H v)⟩) ∧
    StateClass.Rooted (StateClass.ofState ⟨d,C.plug e H,
      (mode,Net.Replacement.host C e H v)⟩) := by
  let F := SingleExpansion.family C e G
  let K := SingleExpansion.family C e H
  have aux (A B) (a : F e = A) (b : K e = B)
      (lc : HoleFree (C.plug e A)) (rc : HoleFree (C.plug e B))
      (root : StateClass.Rooted (StateClass.ofState ⟨d,C.plug e A,
        (mode,Net.Replacement.host C e A v)⟩)) :
      StateClass.machine.Equiv CostOrder.exact
        (StateClass.ofState ⟨d,C.plug e A,(mode,Net.Replacement.host C e A v)⟩)
        (StateClass.ofState ⟨d,C.plug e B,(mode,Net.Replacement.host C e B v)⟩) ∧
      StateClass.Rooted (StateClass.ofState ⟨d,C.plug e B,
        (mode,Net.Replacement.host C e B v)⟩) := by
    subst A; subst B
    let raw := w.singleExpansion C free e
    let lf := ExpandedRewrite.peel C F e (SingleExpansion.retained C e G)
    let rf := ExpandedRewrite.peel C K e (SingleExpansion.retained C e H)
    let cert := raw.congr lf rf
    let q := FillingWitness.plugHost C free e w v
    have label : cert.context.vertexLabel q = .term := by cases v <;> exact typed
    have lp : cert.leftPosition (mode,q) = (mode,Net.Replacement.host C e (F e) v) := by
      have rawPos := FillingWitness.singleExpansion_leftPosition C free e w mode v
      have compose (x : raw.context.Vertex) : cert.leftPosition (mode,x) =
          (mode,Port.map lf.vertices.toFun (raw.leftPosition (mode,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
    have rp : cert.rightPosition (mode,q) = (mode,Net.Replacement.host C e (K e) v) := by
      have rawPos := FillingWitness.singleExpansion_rightPosition C free e w mode v
      have compose (x : raw.context.Vertex) : cert.rightPosition (mode,x) =
          (mode,Port.map rf.vertices.toFun (raw.rightPosition (mode,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
    have lroot : StateClass.Rooted (StateClass.ofState ⟨d,C.plug e (F e),cert.leftPosition (mode,q)⟩) := by
      simpa only [lp] using root
    have rroot := (cert.sharing_rooted_iff trees lc rc 0 (mode,q) nonrewrite).mp lroot
    have eq := pointed_class_exact_equiv_of_left_rooted trees padding cert lc rc
      (mode,q) label nonrewrite lroot
    refine ⟨by simpa only [lp,rp] using eq,?_⟩
    change Search.RootedFrom (C.plug e (K e)) 0 _
    simpa only [rp] using rroot
  exact aux G H (SingleExpansion.selected C e G) (SingleExpansion.selected C e H) left right rooted

end Hypernets.Copying.SharingExecution

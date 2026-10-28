import Hypernets.Copying.BindingFillingWitness
import Hypernets.Copying.AddressedWitness
import Hypernets.Copying.ExpandedRewrite

/-! Binding-free host closure for actual recursively paired fillings. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Casting only the endpoint graph indices leaves the stored shared context
unchanged; the equality proof itself carries no graph transformation. -/
theorem cast_context {d I O} {G H A B : Hypernet d I O}
    (w : FillingWitness T G H) (left : G = A) (right : H = B)
    (eq : FillingWitness T G H = FillingWitness T A B) :
    (cast eq w).context = w.context := by
  cases left; cases right
  have proof : eq = rfl := Subsingleton.elim _ _
  cases proof
  rfl

noncomputable def plug_context_iso {d I O} (C : Hypernet d I O) (free : FocusFree C)
    (e : C.Edge) {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H) :
    DeepIso (w.plug C free e).context (C.plug e w.context) := by
  have eq : (w.plug C free e).context =
      C.expand (SingleExpansion.family C e w.context) := by
    unfold plug singleExpansion
    apply congrArg (Net.expand C)
    funext f
    by_cases selected : f = e
    · subst f
      simp only [dite_true]
      exact (cast_context w (SingleExpansion.selected C e G).symm
        (SingleExpansion.selected C e H).symm
        (by rw [SingleExpansion.selected,SingleExpansion.selected])).trans
          (SingleExpansion.selected C e w.context).symm
    · simp [congr,selected,SingleExpansion.family,of_copies,refl]
  rw [eq]
  exact SingleExpansion.iso C e w.context

/-- Plugging a binding-free residual into an original sourced hole preserves
the exact observation class. -/
theorem plug_binding {d I O} (C : Hypernet d I O) (free : BindingFree C)
    (e : C.Edge) (hole : HoleLabel d (C.edgeLabel e)) (source : ∃ v, v ∈ C.source e)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (binding : BindingFree w.context) : BindingFree (w.plug C free.1 e).context :=
  (BindingFree.iso_iff (plug_context_iso C free.1 e w)).mpr
    (BindingFree.plugAt (.shallow C e) w.context ⟨hole,source⟩ free binding)

/-- Original host coordinates are kept through the two actual expansion
flattenings used by the plugged certificate. -/
def plugHost {d I O} (C : Hypernet d I O) (free : FocusFree C) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (v : C.Vertex) : (w.plug C free e).context.Vertex :=
  match v with
  | .internal x => .internal (.inl x)
  | .input i => .input i
  | .output i => .output i

theorem singleExpansion_leftPosition {d I O} (C : Hypernet d I O) (free : FocusFree C) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (mode : Focus) (v : C.Vertex) :
    (w.singleExpansion C free e).leftPosition (mode,plugHost C free e w v) =
      (mode,Net.Expansion.host C (SingleExpansion.family C e G) v) := by cases v <;> rfl

theorem singleExpansion_rightPosition {d I O} (C : Hypernet d I O) (free : FocusFree C) (e : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (mode : Focus) (v : C.Vertex) :
    (w.singleExpansion C free e).rightPosition (mode,plugHost C free e w v) =
      (mode,Net.Expansion.host C (SingleExpansion.family C e H) v) := by cases v <;> rfl

/-- An actual residual can be placed at any sourced hole in any original
binding-free closing host; the resume token may be internal to that host. -/
theorem plug_binding_quasi {d} (C : Hypernet d [.term] []) (free : BindingFree C)
    (e : C.Edge) (hole : HoleLabel d (C.edgeLabel e)) (source : ∃ v, v ∈ C.source e)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H)
    (binding : BindingFree w.context) (closed : T.OutputClosed)
    (left : HoleFree (C.plug e G)) (right : HoleFree (C.plug e H))
    (v : C.Vertex) (typed : C.vertexLabel v = .term) :
    (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
      (Combined.StateClass.ofState ⟨d,C.plug e G,(.search,Net.Replacement.host C e G v)⟩)
      (Combined.StateClass.ofState ⟨d,C.plug e H,(.search,Net.Replacement.host C e H v)⟩) := by
  let F := SingleExpansion.family C e G
  let K := SingleExpansion.family C e H
  have aux (A B) (a : F e = A) (b : K e = B)
      (lc : HoleFree (C.plug e A)) (rc : HoleFree (C.plug e B)) :
      (Specimens.system T Specimens.bindingFreeContexts closed).Quasi Eq Eq
        (Combined.StateClass.ofState ⟨d,C.plug e A,(.search,Net.Replacement.host C e A v)⟩)
        (Combined.StateClass.ofState ⟨d,C.plug e B,(.search,Net.Replacement.host C e B v)⟩) := by
    subst A; subst B
    let raw := w.singleExpansion C free.1 e
    let lf := Combined.ExpandedRewrite.peel C F e (SingleExpansion.retained C e G)
    let rf := Combined.ExpandedRewrite.peel C K e (SingleExpansion.retained C e H)
    let cert := raw.congr lf rf
    let q := plugHost C free.1 e w v
    have cb : BindingFree cert.context := w.plug_binding C free e hole source binding
    have label : cert.context.vertexLabel q = .term := by cases v <;> exact typed
    have lp : cert.leftPosition (.search,q) = (.search,Net.Replacement.host C e (F e) v) := by
      have rawPos := singleExpansion_leftPosition C free.1 e w .search v
      have compose (x : raw.context.Vertex) : cert.leftPosition (.search,x) =
          (.search,Port.map lf.vertices.toFun (raw.leftPosition (.search,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
    have rp : cert.rightPosition (.search,q) = (.search,Net.Replacement.host C e (K e) v) := by
      have rawPos := singleExpansion_rightPosition C free.1 e w .search v
      have compose (x : raw.context.Vertex) : cert.rightPosition (.search,x) =
          (.search,Port.map rf.vertices.toFun (raw.rightPosition (.search,x)).2) := by cases x <;> rfl
      rw [compose,rawPos]
      cases v <;> rfl
    simpa only [lp,rp] using cert.binding_quasi cb closed lc rc (.search,q) label (by intro eq; cases eq)
  exact aux G H (SingleExpansion.selected C e G) (SingleExpansion.selected C e H) left right

end Hypernets.Copying.FillingWitness

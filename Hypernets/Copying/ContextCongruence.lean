import Hypernets.Copying.DeepComposition
import Hypernets.Copying.Observations

/-! Congruence for concrete graph contexts. Execution's representation law is
explicit: it must be established by the concrete copying machine, not assumed
as a project axiom or confused with a translation theorem. -/
namespace Hypernets.Copying
open Graph

/-- A binding-free graph context whose outer interface may remain open. -/
structure GraphContext (r v a d k h : Nat) where
  graph : Hypernet d [.term] (environmentInterface k h)
  site : Site graph r [.term] (environmentInterface v a)
  sole : SoleHole site
  bindingFree : BindingFree graph

namespace GraphContext
noncomputable def fill {r v a d k h} (C : GraphContext r v a d k h)
    (G : OpenProgram r v a) : OpenProgram d k h where
  graph := plugAt C.site G.graph
  focusFree := focusFree_closed C.site G.graph C.bindingFree.1 G.focusFree
  holeFree := SoleHole.fill_holeFree C.site C.sole G.graph G.holeFree
end GraphContext

/-- Compose a closing context with an open graph context using actual
addressed replacement; the unique remaining hole is the inner occurrence. -/
noncomputable def ClosingContext.compose {r v a d k h}
    (C : ClosingContext d k h) (D : GraphContext r v a d k h) : ClosingContext r v a where
  depth := C.depth
  graph := plugAt C.site D.graph
  site := C.site.comp D.site
  sole := SoleHole.comp C.site D.site C.sole D.sole
  bindingFree := BindingFree.plugAt C.site D.graph
    (SoleHole.sourced C.site C.sole (by decide)) C.bindingFree D.bindingFree

/-- The filled composed context and successive filling differ only by carrier
reassociation, including independently renamed graphs inside boxes. -/
noncomputable def ClosingContext.compose_fill_iso {r v a d k h}
    (C : ClosingContext d k h) (D : GraphContext r v a d k h) (G : OpenProgram r v a) :
    DeepIso ((C.compose D).close G).graph (C.close (D.fill G)).graph :=
  plugAt_assoc C.site D.site G.graph

namespace Execution
variable {State : Type u} (E : Execution State)

/-- Successful termination must not depend on internal carrier names.
The copying machine must prove this representation obligation. -/
def RespectsIso : Prop :=
  ∀ {d} {G H : Hypernet d [.term] []}
    (gf : FocusFree G) (gh : HoleFree G) (hf : FocusFree H) (hh : HoleFree H),
    DeepIso G H → E.machine.Equiv CostOrder.any
      (E.initial ⟨d,G,gf,gh⟩) (E.initial ⟨d,H,hf,hh⟩)

/-- Concrete graph-context congruence follows from proved composition and
associativity, plus execution's explicit invariance under carrier renaming. -/
theorem refines_context (invariant : E.RespectsIso) {r v a d k h}
    (D : GraphContext r v a d k h) {G H : OpenProgram r v a}
    (rel : E.Refines CostOrder.any G H) : E.Refines CostOrder.any (D.fill G) (D.fill H) := by
  intro C
  have gi := invariant ((C.compose D).close G).focusFree ((C.compose D).close G).holeFree
    (C.close (D.fill G)).focusFree (C.close (D.fill G)).holeFree (C.compose_fill_iso D G)
  have hi := invariant ((C.compose D).close H).focusFree ((C.compose D).close H).holeFree
    (C.close (D.fill H)).focusFree (C.close (D.fill H)).holeFree (C.compose_fill_iso D H)
  exact gi.2.trans ((rel (C.compose D)).trans hi.1)

theorem equiv_context (invariant : E.RespectsIso) {r v a d k h}
    (D : GraphContext r v a d k h) {G H : OpenProgram r v a}
    (rel : E.Equiv CostOrder.any G H) : E.Equiv CostOrder.any (D.fill G) (D.fill H) :=
  ⟨E.refines_context invariant D rel.1,E.refines_context invariant D rel.2⟩
end Execution
end Hypernets.Copying

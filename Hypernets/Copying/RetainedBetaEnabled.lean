import Hypernets.Copying.RetainedBetaCanonical
import Hypernets.Copying.BetaEnabled

/-! Retained application frames enable original beta using the actual rooted
stable-argument history. No argument edge belongs to the retained footprint. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening Combined
variable {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))

noncomputable def appOccurrence : Occurrence (primitiveNet (d+1) (.operation .app)) (net B) :=
  Occurrence.primitive (net B) .app rfl

noncomputable def lambdaOccurrence : Occurrence (primitiveNet (d+1) (.operation .lam)) (net B) :=
  Occurrence.primitive (net B) .lam rfl

noncomputable def boxOccurrence : Occurrence (Translation.lambdaBox B) (net B) :=
  Occurrence.labelledCorolla (net B) .box (label B .box) rfl

theorem closure_link (i : Fin ([Wire.thunk 1].length)) :
    (lambdaOccurrence B).ports (.output i) = (boxOccurrence B).ports (.input i) := by
  change Fin 1 at i
  have zero : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem closure_disjoint : ∀ e f, (lambdaOccurrence B).edges e ≠ (boxOccurrence B).edges f := by
  intro e f eq
  cases eq

/-- The complete original closure is extracted from the actual retained
lambda and box, including its full original body and free resource interface. -/
noncomputable def closureOccurrence : Occurrence (lambdaPayload B) (net B) :=
  Occurrence.SerialJoin.occurrence (lambdaOccurrence B) (boxOccurrence B)
    (closure_link B) (closure_disjoint B)

theorem app_input : (appOccurrence B).ports (.input ⟨0,by decide⟩) = .input 0 := rfl

theorem function_link : (appOccurrence B).ports (.output ⟨0,by decide⟩) = (closureOccurrence B).ports (.input 0) := rfl

/-- Every source-relative original opening match is enabled whenever actual
search reaches its rewrite token. The matched argument may belong to a
multi-input shallow parametricity family and is never isolated as a filling. -/
theorem rooted_enabled {I O} (G : Hypernet (d+1) I O) {v : G.Vertex}
    (a : Match G v B) {i : Fin I.length} (rooted : Search.RootedFrom G i (.rewrite,v)) :
    ∃ H : Hypernet (d+1) I O, ∃ w, Rewrite G v H w := by
  let f := occurrence B a
  let app := (appOccurrence B).comp f
  let closure := (closureOccurrence B).comp f
  have linked : app.ports (.output ⟨0,by decide⟩) = closure.ports (.input 0) := congrArg f.ports (function_link B)
  exact Application.rooted_payload_enabled G B app closure linked rooted
end Hypernets.Copying.Application.RetainedFrame

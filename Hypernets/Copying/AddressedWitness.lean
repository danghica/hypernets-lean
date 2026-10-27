import Hypernets.Copying.FillingTransport

/-! Original recursive filling certificates are preserved by replacement at
any addressed occurrence, including occurrences beneath arbitrarily many boxes. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Pair a selected component and retain every other original edge corolla. -/
noncomputable def singleExpansion {d I O} (C : Hypernet d I O) (free : FocusFree C)
    (e : C.Edge) {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H) :
    FillingWitness T (C.expand (SingleExpansion.family C e G))
      (C.expand (SingleExpansion.family C e H)) := by
  classical
  apply expand C
  intro f
  by_cases eq : f = e
  · subst f
    simpa only [SingleExpansion.selected] using w
  · apply of_copies (SingleExpansion.retained C e G f eq)
      (SingleExpansion.retained C e H f eq)
    intro x
    have copy := SingleExpansion.retained C e G f eq
    rw [copy.only x,copy.edge_label]
    exact free f

/-- Single-edge replacement is interpreted by the actual expansion isomorphism. -/
noncomputable def plug {d I O} (C : Hypernet d I O) (free : FocusFree C)
    (e : C.Edge) {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))} (w : FillingWitness T G H) :
    FillingWitness T (C.plug e G) (C.plug e H) :=
  (singleExpansion C free e w).congr (SingleExpansion.iso C e G) (SingleExpansion.iso C e H)

/-- Rebuild an enclosing box with the same binding metadata and outer incidences. -/
noncomputable def replaceBox {d I O} (C : Hypernet (d+1) I O) (free : FocusFree C)
    (e : C.Edge) (b : Box (alphabet d)) (label : C.edgeLabel e = .inr b)
    {G H : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)}
    (w : FillingWitness T G H) :
    FillingWitness T (Copying.replaceBox C e b label G) (Copying.replaceBox C e b label H) :=
  (singleExpansion C free e
    (w.boxedCopies (BoxExpansion.copy C e b label G) (BoxExpansion.copy C e b label H))).congr
      (BoxExpansion.iso C e b label G) (BoxExpansion.iso C e b label H)

/-- Contextual closure uses original filling certificates, with no new
certificate constructor or assumed transitivity. The occurrence need not be shallow. -/
noncomputable def plugAt {d I O} {C : Hypernet d I O} {r J K}
    (site : Site C r J K) (free : FocusFree C) {G H : Hypernet r J K}
    (w : FillingWitness T G H) : FillingWitness T (Copying.plugAt site G) (Copying.plugAt site H) := by
  induction site with
  | shallow C e => exact w.plug C free e
  | @inside d I O C e b label r J K site ih =>
    have bodyFree : FocusFree b.body := by
      have f := free e
      rw [label] at f
      exact f
    exact (ih bodyFree w).replaceBox C free e b label

/-- Every allowed closing observation receives the same genuine paired certificate. -/
noncomputable def closing {r k h} (C : ClosingContext r k h)
    {G H : Hypernet r [.term] (environmentInterface k h)} (w : FillingWitness T G H) :
    FillingWitness T (C.fill G) (C.fill H) := w.plugAt C.site C.bindingFree.1

end Hypernets.Copying.FillingWitness

import Hypernets.Copying.FillingPadding
import Hypernets.Copying.BindingPadding
import Hypernets.Copying.BindingFillingBoxes

/-! Padding certificates together with their actual shared context. The
context reconstruction is certified recursively, so binding freedom can be
transported without relying on an unconstrained choice of filling witness. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Collapse corollas whose labels are recursively equivalent to the original
ones, preserving all incidences and the ordered external interface. -/
def FillingCollapse.related {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (labels : C.Edge → (alphabet d).Symbol) (copies : ∀ e, LabelCopy (F e) (labels e))
    (related : ∀ e, LabelEquiv d (labels e) (C.edgeLabel e)) : DeepIso (C.expand F) C where
  vertices := FillingCollapse.vertices C F labels copies
  edges := FillingCollapse.edges C F labels copies
  internal_label v := by
    rcases v with v | ⟨e,v⟩
    · rfl
    · exact False.elim ((copies e).no_internal v)
  edge_label x := by
    obtain ⟨e,x⟩ := x
    change LabelEquiv d ((F e).edgeLabel x) (C.edgeLabel e)
    rw [(copies e).only x,(copies e).edge_label]
    exact related e
  source x := FillingCollapse.source C F labels copies x.1 x.2
  target x := FillingCollapse.target C F labels copies x.1 x.2

namespace FillingWitness
variable {T : PreTemplate}

/-- A component's shared context is a single corolla, with a recursively
equivalent label. This records the original shallow-hole geometry. -/
structure CorollaContext {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (original : (alphabet d).Symbol) where
  label : (alphabet d).Symbol
  copy : LabelCopy w.context label
  related : LabelEquiv d label original

def CorollaContext.reboundary {d I O J K} {G H : Hypernet d I O}
    {w : FillingWitness T G H} {original} (c : CorollaContext w original)
    (hi : I = J) (ho : O = K) : CorollaContext (w.reboundary hi ho) original := by
  refine ⟨c.label,?_,c.related⟩
  rw [reboundary_context]
  exact c.copy.reboundary hi ho

def of_copies_context {d I O} {G H : Hypernet d I O} {a}
    (l : LabelCopy G a) (r : LabelCopy H a) (free : FocusFree G) :
    CorollaContext (of_copies (T := T) l r free) a :=
  ⟨a,l,labelEquiv_refl d a⟩

def of_rel_context {d I O} {G H : Hypernet d I O} (name : Nat) (rel : T.Rel G H) :
    CorollaContext (of_rel name rel) (primitiveLabel d (.hole ⟨name,I,O⟩)) := by
  cases d <;> exact ⟨_,LabelCopy.corolla _,labelEquiv_refl _ _⟩

/-- Reassembly retains precisely the padded original context, up to recursive
carrier representation, whenever each padded component has its original corolla. -/
noncomputable def paddedExpansion_context {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (Padding.graph (L e)) (Padding.graph (R e)))
    (c : ∀ e, CorollaContext (w e) (Padding.label d (C.edgeLabel e))) :
    DeepIso (paddedExpansion C w).context (Padding.graph C) := by
  let casted := fun e => (c e).reboundary
    (Padding.label_input d (C.edgeLabel e)).symm (Padding.label_output d (C.edgeLabel e)).symm
  exact FillingCollapse.related (Padding.graph C) _
    (fun e => (casted e).label) (fun e => (casted e).copy) (fun e => (casted e).related)

/-- A padded shallow hole is the same named, typed hole. -/
noncomputable def paddedHole_context (closed : T.PaddingClosed) {d I O}
    (C : Hypernet d I O) (e : C.Edge)
    {L R : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (h : Hole) (label : C.edgeLabel e = primitiveLabel d (.hole h)) (rel : T.Rel L R) :
    Σ next : FillingWitness T (Padding.graph L) (Padding.graph R),
      CorollaContext next (Padding.label d (C.edgeLabel e)) := by
  have rel' : T.Rel (Padding.graph L) (Padding.graph R) := by
    simpa only [Padding.graph_eq_raise] using closed rel
  have same : primitiveLabel (d+1) (.hole ⟨h.name,
      (alphabet d).signature.input (C.edgeLabel e),
      (alphabet d).signature.output (C.edgeLabel e)⟩) = Padding.label d (C.edgeLabel e) := by
    rw [label]
    cases d <;> rfl
  exact ⟨of_rel h.name rel', same ▸ of_rel_context h.name rel'⟩

/-- Padding rebuilds a witness together with an isomorphism from its actual
shared context to the padded original context. The boxed case descends only
through original boxed certificates, preserving their binding metadata. -/
theorem raisedContext_exists (closed : T.PaddingClosed) {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) :
    Nonempty (Σ next : FillingWitness T (Copying.raise d G) (Copying.raise d H),
      DeepIso next.context (Copying.raise d w.context)) := by
  induction d generalizing I O with
  | zero =>
    have each (e : w.context.Edge) :
        Nonempty (Σ next : FillingWitness T (Padding.graph (w.left e)) (Padding.graph (w.right e)),
          CorollaContext next (Padding.label 0 (w.context.edgeLabel e))) := by
      cases w.edges e with
      | retained l r =>
        have free : FocusFree (Padding.graph (w.left e)) := by
          simpa only [FocusFree,Padding.graph_eq_raise] using
            (allLabels_raise_iff _ _ _).mpr (l.focusFree (w.free e))
        exact ⟨⟨of_copies l.padding r.padding free,of_copies_context l.padding r.padding free⟩⟩
      | filled h label rel => exact ⟨paddedHole_context closed w.context e h label rel⟩
    let parts := fun e => Classical.choice (each e)
    let next := (paddedExpansion w.context (fun e => (parts e).1)).congr
      (Combined.graphIso w.leftIso) (Combined.graphIso w.rightIso)
    have result : Nonempty (Σ v : FillingWitness T (Padding.graph G) (Padding.graph H),
        DeepIso v.context (Padding.graph w.context)) :=
      ⟨⟨next,paddedExpansion_context w.context (fun e => (parts e).1) (fun e => (parts e).2)⟩⟩
    rw [Padding.graph_eq_raise G,Padding.graph_eq_raise H,Padding.graph_eq_raise w.context] at result
    exact result
  | succ d ih =>
    have each (e : w.context.Edge) :
        Nonempty (Σ next : FillingWitness T (Padding.graph (w.left e)) (Padding.graph (w.right e)),
          CorollaContext next (Padding.label (d+1) (w.context.edgeLabel e))) := by
      cases w.edges e with
      | retained l r =>
        have free : FocusFree (Padding.graph (w.left e)) := by
          simpa only [FocusFree,Padding.graph_eq_raise] using
            (allLabels_raise_iff _ _ _).mpr (l.focusFree (w.free e))
        exact ⟨⟨of_copies l.padding r.padding free,of_copies_context l.padding r.padding free⟩⟩
      | filled h label rel => exact ⟨paddedHole_context closed w.context e h label rel⟩
      | boxed b label inner l r =>
        have free : FocusFree b.body := by have hf := w.free e; rw [label] at hf; exact hf
        cases inner with
        | expand C F K cert =>
          let base : FillingWitness T (b.body.expand F) (b.body.expand K) :=
            ⟨b.body,free,F,K,cert,DeepIso.refl _,DeepIso.refl _⟩
          obtain ⟨⟨body,contextIso⟩⟩ := ih base
          let next := boxedCopies body l.padding r.padding
          refine ⟨⟨next,⟨.inr ⟨b.bound,b.freeVariables,b.freeAtoms,body.context⟩,
            boxedCopies_contextCopy body l.padding r.padding,?_⟩⟩⟩
          rw [label]
          exact BoxRelated.bodies ⟨contextIso⟩
    let parts := fun e => Classical.choice (each e)
    let next := (paddedExpansion w.context (fun e => (parts e).1)).congr
      (Combined.graphIso w.leftIso) (Combined.graphIso w.rightIso)
    have result : Nonempty (Σ v : FillingWitness T (Padding.graph G) (Padding.graph H),
        DeepIso v.context (Padding.graph w.context)) :=
      ⟨⟨next,paddedExpansion_context w.context (fun e => (parts e).1) (fun e => (parts e).2)⟩⟩
    rw [Padding.graph_eq_raise G,Padding.graph_eq_raise H,Padding.graph_eq_raise w.context] at result
    exact result

/-- Choose the padded certificate and its context isomorphism as one object. -/
noncomputable def raiseWithContext (closed : T.PaddingClosed) {d I O}
    {G H : Hypernet d I O} (w : FillingWitness T G H) :
    Σ next : FillingWitness T (Copying.raise d G) (Copying.raise d H),
      DeepIso next.context (Copying.raise d w.context) :=
  Classical.choice (raisedContext_exists closed w)

/-- Binding freedom follows from the preserved shared context, not from the
filled endpoints or from an arbitrary witness choice. -/
noncomputable def raiseBinding (closed : T.PaddingClosed) {d I O}
    {G H : Hypernet d I O} (w : FillingWitness T G H) (binding : BindingFree w.context) :
    {next : FillingWitness T (Copying.raise d G) (Copying.raise d H) // BindingFree next.context} :=
  ⟨(w.raiseWithContext closed).1,
    (BindingFree.iso_iff (w.raiseWithContext closed).2).mpr
      ((BindingFree.raise_iff d w.context).mpr binding)⟩

end FillingWitness
end Hypernets.Copying

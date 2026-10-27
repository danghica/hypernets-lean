import Hypernets.Copying.FillingWitness

/-! Assembly of genuine recursive filling certificates. Flattening is proved
by explicit carrier isomorphisms, not added as a certificate constructor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Paired components may already contain arbitrarily deep filled boxes. -/
def expand {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) : FillingWitness T (C.expand G) (C.expand H) where
  context := C.expand (fun e => (w e).context)
  free := Serial.allLabels_expand _ C _ (fun e => (w e).free)
  left := Net.ExpansionAssoc.flat C (fun e => (w e).context) (fun e => (w e).left)
  right := Net.ExpansionAssoc.flat C (fun e => (w e).context) (fun e => (w e).right)
  edges x := by
    rcases x with ⟨e,x⟩
    cases (w e).edges x with
    | retained l r => exact .retained l r
    | filled h label rel => exact .filled h label rel
    | boxed b label inner l r => exact .boxed b label inner l r
  leftIso := (DeepIso.ofIso (Net.ExpansionAssoc.iso C _ (fun e => (w e).left))).trans
    (Net.ExpansionIso.iso C (fun e => (w e).leftIso))
  rightIso := (DeepIso.ofIso (Net.ExpansionAssoc.iso C _ (fun e => (w e).right))).trans
    (Net.ExpansionIso.iso C (fun e => (w e).rightIso))

/-- Branch tags and all boundary positions follow the chosen original shuffle. -/
def parallel {d : Nat} {A : Type} {I O : A → List Wire} {J K : List Wire}
    {G H : ∀ a, Hypernet d (I a) (O a)} (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration A) (w : ∀ a, FillingWitness T (G a) (H a)) :
    FillingWitness T (Net.Parallel.net G B finite) (Net.Parallel.net H B finite) where
  context := Net.Parallel.net (fun a => (w a).context) B finite
  free x := (w x.1).free x.2
  left := Net.ParallelExpansion.family _ B finite (fun a => (w a).left)
  right := Net.ParallelExpansion.family _ B finite (fun a => (w a).right)
  edges x := by
    rcases x with ⟨a,x⟩
    cases (w a).edges x with
    | retained l r => exact .retained l r
    | filled h label rel => exact .filled h label rel
    | boxed b label inner l r => exact .boxed b label inner l r
  leftIso := (DeepIso.ofIso (Net.ParallelExpansion.iso _ B finite (fun a => (w a).left))).trans
    (Net.ParallelIso.iso (fun a => (w a).leftIso) B finite)
  rightIso := (DeepIso.ofIso (Net.ParallelExpansion.iso _ B finite (fun a => (w a).right))).trans
    (Net.ParallelIso.iso (fun a => (w a).rightIso) B finite)

/-- Ordered binary parallel assembly retains both independent recursive certificates. -/
def tensor {d I O J K} {G G' : Hypernet d I O} {H H' : Hypernet d J K}
    (g : FillingWitness T G G') (h : FillingWitness T H H') :
    FillingWitness T (Net.Tensor.net G H) (Net.Tensor.net G' H') := by
  apply parallel (Net.Tensor.boundary I O J K)
  intro b; cases b
  · exact g
  · exact h

/-- Shared-interface gluing flattens the two existing certificates. -/
def serial {d I J O} {G G' : Hypernet d I J} {H H' : Hypernet d J O}
    (g : FillingWitness T G G') (h : FillingWitness T H H') :
    FillingWitness T (Serial.net G H) (Serial.net G' H') := by
  apply expand (Serial.pattern d I J O)
  intro b
  cases d <;> cases b
  all_goals first | exact g | exact h

/-- Rebuild an original box from its paired bodies, preserving its exact binder metadata. -/
def boxed {d n k h} {G H : Hypernet d [.term] (environmentInterface (n+k) h)}
    (w : FillingWitness T G H) :
    FillingWitness T (box (bound := n) (freeVariables := k) G) (box (bound := n) (freeVariables := k) H) where
  context := box w.context
  free _ := w.free
  left _ := box (w.context.expand w.left)
  right _ := box (w.context.expand w.right)
  edges _ := .boxed ⟨n,k,h,w.context⟩ rfl w.paired (LabelCopy.corolla _) (LabelCopy.corolla _)
  leftIso := (DeepIso.ofIso (FillingCollapse.relabel (box w.context) _
    (fun _ => .inr ⟨n,k,h,w.context.expand w.left⟩) (fun _ => LabelCopy.corolla _)
    (fun _ => rfl) (fun _ => rfl))).trans (box_congr w.leftIso)
  rightIso := (DeepIso.ofIso (FillingCollapse.relabel (box w.context) _
    (fun _ => .inr ⟨n,k,h,w.context.expand w.right⟩) (fun _ => LabelCopy.corolla _)
    (fun _ => rfl) (fun _ => rfl))).trans (box_congr w.rightIso)
end Hypernets.Copying.FillingWitness

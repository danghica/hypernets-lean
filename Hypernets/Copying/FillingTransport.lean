import Hypernets.Copying.CopyResidualExamples

/-! Corolla representation and interface transport for recursive filling data. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace LabelCopy

/-- A copied corolla's ordered boundary is exactly its label signature. -/
theorem input {d I O} {G : Hypernet d I O} {a} (c : LabelCopy G a) :
    (alphabet d).signature.input a = I := by
  rw [← c.edge_label,← G.source_typed,c.source]
  simp [Port.label,List.finRange,List.map_ofFn,List.ofFn_getElem,Function.comp_def]

theorem output {d I O} {G : Hypernet d I O} {a} (c : LabelCopy G a) :
    (alphabet d).signature.output a = O := by
  rw [← c.edge_label,← G.target_typed,c.target]
  simp [Port.label,List.finRange,List.map_ofFn,List.ofFn_getElem,Function.comp_def]

/-- Renaming corolla carriers does not add vertices, edges, or reorder ports. -/
def iso {d I O} {G H : Hypernet d I O} {a b}
    (c : LabelCopy G a) (e : LabelCopy H b) (labels : LabelEquiv d a b) : DeepIso G H where
  vertices := {
    toFun v := False.elim (c.no_internal v)
    invFun v := False.elim (e.no_internal v)
    left_inv v := False.elim (c.no_internal v)
    right_inv v := False.elim (e.no_internal v) }
  edges := {
    toFun _ := e.edge
    invFun _ := c.edge
    left_inv x := (c.only x).symm
    right_inv x := (e.only x).symm }
  internal_label v := False.elim (c.no_internal v)
  edge_label x := by simpa only [c.only x,c.edge_label,e.edge_label] using labels
  source x := by rw [c.only x,c.source,e.source,List.map_map]; rfl
  target x := by rw [c.only x,c.target,e.target,List.map_map]; rfl

/-- Uniform padding retains the literal corolla certificate. -/
def padding {d I O} {G : Hypernet d I O} {a} (c : LabelCopy G a) :
    LabelCopy (Padding.graph G) (Padding.label d a) where
  edge := c.edge
  edge_label := congrArg (Padding.label d) c.edge_label
  source := by simpa [Padding.graph,Net.relabel,Port.map_id_fun] using c.source
  target := by simpa [Padding.graph,Net.relabel,Port.map_id_fun] using c.target
  only := c.only
end LabelCopy

namespace FillingWitness
variable {T : PreTemplate}

/-- Two differently named copies of one label share its reflexive filling. -/
def of_copies {d I O} {G H : Hypernet d I O} {a}
    (l : LabelCopy G a) (r : LabelCopy H a) (free : FocusFree G) : FillingWitness T G H :=
  (refl G free).congr (DeepIso.refl _) (l.iso r (labelEquiv_refl _ _))

/-- A paired body certificate reconstructs arbitrarily represented literal
box corollas at their original external interfaces. -/
def boxedCopies {d I O n k h} {L R : Hypernet d [.term] (environmentInterface (n+k) h)}
    {G H : Hypernet (d+1) I O} (w : FillingWitness T L R)
    (l : LabelCopy G (.inr ⟨n,k,h,L⟩)) (r : LabelCopy H (.inr ⟨n,k,h,R⟩)) :
    FillingWitness T G H := by
  have hi : [.thunk n] = I := l.input
  have ho : environmentInterface k h = O := l.output
  exact (w.boxed.reboundary hi ho).congr
    ((LabelCopy.corolla (d := d+1) (.inr ⟨n,k,h,L⟩)).reboundary hi ho |>.iso l (labelEquiv_refl _ _))
    ((LabelCopy.corolla (d := d+1) (.inr ⟨n,k,h,R⟩)).reboundary hi ho |>.iso r (labelEquiv_refl _ _))
end FillingWitness
end Hypernets.Copying

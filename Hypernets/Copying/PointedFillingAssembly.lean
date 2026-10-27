import Hypernets.Copying.CorollaNormalisation

/-! Residual certificates assembled at the actual resumed token. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.PointedFilling
open Graph Combined

/-- Flatten paired components while retaining a token inside the selected
component's common context, rather than requiring it to be an outer host wire. -/
def expandAt {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness template (G e) (H e)) (e : C.Edge) (v : (w e).context.Vertex) :
    PointedFilling (C.expand G) (Net.Expansion.insert C G e ((w e).leftPosition (.search,v)).2)
      (C.expand H) (Net.Expansion.insert C H e ((w e).rightPosition (.search,v)).2) where
  filling := FillingWitness.expand C w
  point := Net.Expansion.insert C (fun e => (w e).context) e v
  left := by
    cases v with
    | internal v => rfl
    | input i => exact congrArg Prod.snd (FillingWitness.expand_leftPosition C w .search (C.sourcePort e i))
    | output i => exact congrArg Prod.snd (FillingWitness.expand_leftPosition C w .search (C.targetPort e i))
  right := by
    cases v with
    | internal v => rfl
    | input i => exact congrArg Prod.snd (FillingWitness.expand_rightPosition C w .search (C.sourcePort e i))
    | output i => exact congrArg Prod.snd (FillingWitness.expand_rightPosition C w .search (C.targetPort e i))

/-- A pointed certificate yields the actual original quasi-specimen, with
rootedness handled by its original definition. -/
theorem quasi {d} {G H : Hypernet d [.term] []} {v w} (p : PointedFilling G v H w)
    (leftClosed : HoleFree G) (rightClosed : HoleFree H) (typed : G.vertexLabel v = .term) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  have lt : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rt : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  have label : p.filling.context.vertexLabel p.point = .term := by
    have h := (BoundaryIso.ofDeepIso p.filling.leftIso).vertex_label
      (Net.Expansion.host p.filling.context p.filling.left p.point)
    change G.vertexLabel (p.filling.leftPosition (.search,p.point)).2 = _ at h
    rw [p.left] at h
    exact (Net.Expansion.host_label p.filling.context p.filling.left p.point).symm.trans (h.symm.trans typed)
  simpa only [lt,rt] using p.filling.quasi template_outputClosed leftClosed rightClosed
    (.search,p.point) label (by intro eq; cases eq)
end Hypernets.Copying.BoxPermutation.PointedFilling

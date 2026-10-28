import Hypernets.Copying.BindingSinkReplacement
import Hypernets.Copying.RetainedFootprintFrame
import Hypernets.Copying.RewriteCutFactorization

/-! Sink admissibility applies to actual machine successors and to the common
frame constructed for paired operational fillings. In particular arithmetic
needs neither a rootedness assumption nor a binding-free auxiliary cut. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace Opening.Occurrence
variable {d I O J} {A B : Hypernet d J []} {G H : Hypernet d I O}
    (f : Occurrence A G)

/-- An independently presented successor inherits admissibility from the
explicit sink replacement by the proved pointed successor isomorphism. -/
theorem bindingFree_rewrite_sink {a : A.Vertex} {b : B.Vertex} {v : H.Vertex}
    (free : BindingFree G) (focus : FocusFree B) (closed : HoleFree B)
    (localStep : Rewrite A a B b) (actual : Rewrite G (f.ports a) H v) : BindingFree H := by
  obtain ⟨iso⟩ := f.rewrite_successor localStep actual
  exact (BindingFree.iso_iff iso.graph).mpr
    (CompleteMatchCut.bindingFree_replace_sink f.matchEmbedding f.label B free focus closed)

end Opening.Occurrence

namespace RetainedFootprint
variable {d I O J} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {A : Hypernet d J []} (f : Opening.Occurrence A (C.expand L))
    {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f.matchEmbedding)

/-- The actual grafted common context is binding-free when the local residual
is a closed sink. The original common context supplies the path restriction;
no binding-free condition is imposed on the computed auxiliary frame. -/
theorem frame_plug_bindingFree_sink (B : Hypernet d J [])
    (free : BindingFree C) (focus : FocusFree B) (closed : HoleFree B) :
    BindingFree ((frame C f cert avoid).plug none
      (B.reboundary (CompleteMatchCut.hole_input _ _).symm (CompleteMatchCut.hole_output _ _).symm)) :=
  CompleteMatchCut.bindingFree_replace_sink
    (skeletonOccurrence C f cert avoid).matchEmbedding (skeletonOccurrence C f cert avoid).label
    B free focus closed

end RetainedFootprint

namespace Arithmetic

/-- Actual unary arithmetic preserves binding-free common contexts. -/
theorem unary_bindingFree {d I O n} {G H : Hypernet d I O}
    (f : Opening.Occurrence (unaryBefore d n) G) (free : BindingFree G)
    {v : H.Vertex} (actual : Rewrite G (f.ports (.input 0)) H v) : BindingFree H :=
  f.bindingFree_rewrite_sink free (safe_number d (neg n)).1 (safe_number d (neg n)).2
    (.local (.unaryArithmetic d n)) actual

/-- The same concrete path argument covers both addition and truncated subtraction. -/
theorem binary_bindingFree {d I O m n} (o : BinaryCode) {G H : Hypernet d I O}
    (f : Opening.Occurrence (binaryBefore o d m n) G) (free : BindingFree G)
    {v : H.Vertex} (actual : Rewrite G (f.ports (.input 0)) H v) : BindingFree H :=
  f.bindingFree_rewrite_sink free (safe_number d (o.eval m n)).1 (safe_number d (o.eval m n)).2
    (.local (.binaryArithmetic o d m n)) actual

end Arithmetic
end Hypernets.Copying

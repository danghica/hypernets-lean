import Hypernets.Copying.OriginalEdgeWitness

/-! Exact token transport for boundary reindexing and simultaneous assembly of
arbitrary original recursive filling witnesses. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

theorem cast_leftPosition {d I O} {G H A B : Hypernet d I O}
    (w : FillingWitness T G H) (left : G = A) (right : H = B)
    (eq : FillingWitness T G H = FillingWitness T A B) (mode) (v : w.context.Vertex) :
    (cast eq w).leftPosition (mode,Port.map (cast (congrArg Net.Internal
      (cast_context w left right eq).symm)) v) =
      (mode,Port.map (cast (congrArg Net.Internal left)) (w.leftPosition (mode,v)).2) := by
  cases left; cases right
  have proof : eq = rfl := Subsingleton.elim _ _
  cases proof
  cases v <;> rfl

theorem cast_rightPosition {d I O} {G H A B : Hypernet d I O}
    (w : FillingWitness T G H) (left : G = A) (right : H = B)
    (eq : FillingWitness T G H = FillingWitness T A B) (mode) (v : w.context.Vertex) :
    (cast eq w).rightPosition (mode,Port.map (cast (congrArg Net.Internal
      (cast_context w left right eq).symm)) v) =
      (mode,Port.map (cast (congrArg Net.Internal right)) (w.rightPosition (mode,v)).2) := by
  cases left; cases right
  have proof : eq = rfl := Subsingleton.elim _ _
  cases proof
  cases v <;> rfl

noncomputable def reboundaryVertex {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (v : w.context.Vertex) :
    (w.reboundary hi ho).context.Vertex :=
  Port.map (cast (congrArg Net.Internal (w.reboundary_context hi ho).symm)) (Port.cast hi ho v)

theorem reboundary_leftPosition {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (mode) (v : w.context.Vertex) :
    (w.reboundary hi ho).leftPosition (mode,reboundaryVertex w hi ho v) =
      (mode,Port.cast hi ho (w.leftPosition (mode,v)).2) := by
  cases hi; cases ho
  have h := cast_leftPosition w (Net.reboundary_refl G).symm (Net.reboundary_refl H).symm
    (by rw [Net.reboundary_refl,Net.reboundary_refl]) mode v
  cases v with
  | internal v => simpa [reboundaryVertex,reboundary,Port.cast,leftPosition,Net.Expansion.host,Port.map] using h
  | input i => simp [reboundaryVertex,Port.cast,leftPosition,Net.Expansion.host,Port.map]
  | output i => simp [reboundaryVertex,Port.cast,leftPosition,Net.Expansion.host,Port.map]

theorem reboundary_rightPosition {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (mode) (v : w.context.Vertex) :
    (w.reboundary hi ho).rightPosition (mode,reboundaryVertex w hi ho v) =
      (mode,Port.cast hi ho (w.rightPosition (mode,v)).2) := by
  cases hi; cases ho
  have h := cast_rightPosition w (Net.reboundary_refl G).symm (Net.reboundary_refl H).symm
    (by rw [Net.reboundary_refl,Net.reboundary_refl]) mode v
  cases v with
  | internal v => simpa [reboundaryVertex,reboundary,Port.cast,rightPosition,Net.Expansion.host,Port.map] using h
  | input i => simp [reboundaryVertex,Port.cast,rightPosition,Net.Expansion.host,Port.map]
  | output i => simp [reboundaryVertex,Port.cast,rightPosition,Net.Expansion.host,Port.map]

theorem leftPosition_label {d I O} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (mode) (v : w.context.Vertex) :
    G.vertexLabel (w.leftPosition (mode,v)).2 = w.context.vertexLabel v :=
  ((BoundaryIso.ofDeepIso w.leftIso).vertex_label _).trans
    (Net.Expansion.host_label w.context w.left v)

theorem reboundaryVertex_label {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) (v : w.context.Vertex) :
    (w.reboundary hi ho).context.vertexLabel (reboundaryVertex w hi ho v) = w.context.vertexLabel v := by
  rw [← leftPosition_label (w.reboundary hi ho) .search,reboundary_leftPosition]
  have labels (x : G.Vertex) : (G.reboundary hi ho).vertexLabel (Port.cast hi ho x) = G.vertexLabel x := by
    cases hi; cases ho; cases x <;> rfl
  exact (labels _).trans (leftPosition_label w .search v)

theorem expand_selected_leftPosition {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (mode) (e : C.Edge) (v : (w e).context.Vertex) :
    (expand C w).leftPosition (mode,Net.Expansion.insert C (fun e => (w e).context) e v) =
      (mode,Net.Expansion.insert C G e ((w e).leftPosition (mode,v)).2) := by
  cases v with
  | internal v => rfl
  | input i => exact expand_leftPosition C w mode (C.sourcePort e i)
  | output i => exact expand_leftPosition C w mode (C.targetPort e i)

theorem expand_selected_rightPosition {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (mode) (e : C.Edge) (v : (w e).context.Vertex) :
    (expand C w).rightPosition (mode,Net.Expansion.insert C (fun e => (w e).context) e v) =
      (mode,Net.Expansion.insert C H e ((w e).rightPosition (mode,v)).2) := by
  cases v with
  | internal v => rfl
  | input i => exact expand_rightPosition C w mode (C.sourcePort e i)
  | output i => exact expand_rightPosition C w mode (C.targetPort e i)

end Hypernets.Copying.FillingWitness

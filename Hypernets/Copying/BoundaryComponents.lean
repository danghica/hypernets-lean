import Hypernets.Copying.AtomicRenaming

/-! Extract the three disjoint carrier bijections of a boundary isomorphism. -/
namespace Hypernets.Copying.BoundaryIso
open Graph
variable {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}

def internalMap (f : BoundaryIso G H) (v : G.Internal) : H.Internal :=
  match h : f.ports.toFun (.internal v) with
  | .internal w => w
  | .input _ => False.elim ((f.input_iff (.internal v)).mp (by rw [h]; trivial))
  | .output _ => False.elim ((f.output_iff (.internal v)).mp (by rw [h]; trivial))

theorem map_internal (f : BoundaryIso G H) (v : G.Internal) :
    f.ports.toFun (.internal v) = .internal (internalMap f v) := by
  unfold internalMap
  split
  · assumption
  · rename_i w eq; have := f.input_iff (.internal v); simp [eq,Port.IsInput] at this
  · rename_i w eq; have := f.output_iff (.internal v); simp [eq,Port.IsOutput] at this

def inputMap (f : BoundaryIso G H) (i : Fin I.length) : Fin J.length :=
  match h : f.ports.toFun (.input i) with
  | .input j => j
  | .internal _ => False.elim (by have := (f.input_iff _).mpr (show (Port.input i : G.Vertex).IsInput from trivial); rw [h] at this; exact this)
  | .output _ => False.elim (by have := (f.input_iff _).mpr (show (Port.input i : G.Vertex).IsInput from trivial); rw [h] at this; exact this)

theorem map_input (f : BoundaryIso G H) (i : Fin I.length) :
    f.ports.toFun (.input i) = .input (inputMap f i) := by
  unfold inputMap
  split
  · assumption
  all_goals rename_i w eq; have := f.input_iff (.input i); simp [eq,Port.IsInput] at this

def outputMap (f : BoundaryIso G H) (i : Fin O.length) : Fin K.length :=
  match h : f.ports.toFun (.output i) with
  | .output j => j
  | .internal _ => False.elim (by have := (f.output_iff _).mpr (show (Port.output i : G.Vertex).IsOutput from trivial); rw [h] at this; exact this)
  | .input _ => False.elim (by have := (f.output_iff _).mpr (show (Port.output i : G.Vertex).IsOutput from trivial); rw [h] at this; exact this)

theorem map_output (f : BoundaryIso G H) (i : Fin O.length) :
    f.ports.toFun (.output i) = .output (outputMap f i) := by
  unfold outputMap
  split
  · assumption
  all_goals rename_i w eq; have := f.output_iff (.output i); simp [eq,Port.IsOutput] at this

def internals (f : BoundaryIso G H) : Bijection G.Internal H.Internal where
  toFun := internalMap f
  invFun := internalMap f.symm
  left_inv v := by
    apply Port.internal.inj (inputs := I.length) (outputs := O.length)
    rw [← map_internal,← map_internal]
    exact f.ports.left_inv _
  right_inv v := by
    apply Port.internal.inj (inputs := J.length) (outputs := K.length)
    rw [← map_internal,← map_internal]
    exact f.ports.right_inv _

def inputs (f : BoundaryIso G H) : Bijection (Fin I.length) (Fin J.length) where
  toFun := inputMap f
  invFun := inputMap f.symm
  left_inv i := by
    apply Port.input.inj (Internal := G.Internal) (outputs := O.length)
    rw [← map_input,← map_input]
    exact f.ports.left_inv _
  right_inv i := by
    apply Port.input.inj (Internal := H.Internal) (outputs := K.length)
    rw [← map_input,← map_input]
    exact f.ports.right_inv _

def outputs (f : BoundaryIso G H) : Bijection (Fin O.length) (Fin K.length) where
  toFun := outputMap f
  invFun := outputMap f.symm
  left_inv i := by
    apply Port.output.inj (Internal := G.Internal) (inputs := I.length)
    rw [← map_output,← map_output]
    exact f.ports.left_inv _
  right_inv i := by
    apply Port.output.inj (Internal := H.Internal) (inputs := J.length)
    rw [← map_output,← map_output]
    exact f.ports.right_inv _

theorem internal_label (f : BoundaryIso G H) (v : G.Internal) :
    H.internalLabel (f.internals.toFun v) = G.internalLabel v := by
  have h := f.vertex_label (.internal v)
  rw [map_internal] at h
  exact h

theorem input_label (f : BoundaryIso G H) (i : Fin I.length) : J[f.inputs.toFun i] = I[i] := by
  have h := f.vertex_label (.input i)
  rw [map_input] at h
  exact h

theorem output_label (f : BoundaryIso G H) (i : Fin O.length) : K[f.outputs.toFun i] = O[i] := by
  have h := f.vertex_label (.output i)
  rw [map_output] at h
  exact h
end Hypernets.Copying.BoundaryIso

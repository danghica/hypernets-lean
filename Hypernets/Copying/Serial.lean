import Hypernets.Copying.Predicates
import Hypernets.Graph.Simultaneous

/-! Serial composition by an explicit two-hole pattern. Expanding the two
holes connects each left output to the corresponding right input. -/
namespace Hypernets.Copying
open Graph
namespace Serial

/-- The left and right slots are distinct even when their interfaces coincide. -/
def hole (I J K : List Wire) : Bool → Hole
  | false => ⟨0,I,J⟩
  | true => ⟨1,J,K⟩

/-- Two-hole wiring pattern with the common interface represented internally. -/
@[reducible] def pattern (d : Nat) (I J K : List Wire) : Hypernet d I K where
  Internal := Fin J.length
  Edge := Bool
  finiteInternal := Enumeration.fin J.length
  finiteEdge := ⟨[false,true],by intro b; cases b <;> simp⟩
  internalLabel i := J[i]
  edgeLabel b := primitiveLabel d (.hole (hole I J K b))
  source
    | false => (List.finRange I.length).map Port.input
    | true => (List.finRange J.length).map Port.internal
  target
    | false => (List.finRange J.length).map Port.internal
    | true => (List.finRange K.length).map Port.output
  source_nodup b := by
    cases b
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.input.inj h)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.internal.inj h)
  target_nodup b := by
    cases b
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.internal.inj h)
    · exact nodup_map_on (finRange_nodup _) (fun _ _ _ _ h => Port.output.inj h)
  source_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all
    all_goals obtain ⟨a,rfl⟩ := he; simp at hf
  target_unique := by
    intro v e f he hf
    cases e <;> cases f <;> simp_all
    all_goals obtain ⟨a,rfl⟩ := he; simp at hf
  source_coverage := by
    intro v
    cases v with
    | internal v =>
      constructor
      · intro _; simp [Port.IsOutput]
      · intro _; exact ⟨true,List.mem_map_of_mem (List.mem_finRange v)⟩
    | input v =>
      constructor
      · intro _; simp [Port.IsOutput]
      · intro _; exact ⟨false,List.mem_map_of_mem (List.mem_finRange v)⟩
    | output v =>
      constructor
      · rintro ⟨b,h⟩; cases b <;> simp at h
      · intro h; exact False.elim (h trivial)
  target_coverage := by
    intro v
    cases v with
    | internal v =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _; exact ⟨false,List.mem_map_of_mem (List.mem_finRange v)⟩
    | output v =>
      constructor
      · intro _; simp [Port.IsInput]
      · intro _; exact ⟨true,List.mem_map_of_mem (List.mem_finRange v)⟩
    | input v =>
      constructor
      · rintro ⟨b,h⟩; cases b <;> simp at h
      · intro h; exact False.elim (h trivial)
  source_typed b := by
    cases b <;> simp [primitive_input, primitiveSignature, hole, List.finRange,
      List.map_ofFn, Port.label, Function.comp_def, List.ofFn_getElem]
  target_typed b := by
    cases b <;> simp [primitive_output, primitiveSignature, hole, List.finRange,
      List.map_ofFn, Port.label, Function.comp_def, List.ofFn_getElem]

/-- Each shared output and input denotes the same internal pattern vertex. -/
theorem interface_connection (d : Nat) (I J K : List Wire) (j : Fin J.length) :
    (pattern d I J K).targetPort false ⟨j.val,by simpa [primitive_output, primitiveSignature, hole] using j.isLt⟩ =
    (pattern d I J K).sourcePort true ⟨j.val,by simpa [primitive_input, primitiveSignature, hole] using j.isLt⟩ := by
  simp [Net.targetPort, Net.sourcePort, pattern, List.finRange]

/-- Assign the two graphs to their exact pattern interfaces. -/
def filling {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) (b : Bool) :
    Hypernet d ((alphabet d).signature.input ((pattern d I J K).edgeLabel b))
      ((alphabet d).signature.output ((pattern d I J K).edgeLabel b)) := by
  cases b
  · simpa [pattern, primitive_input, primitive_output, primitiveSignature, hole] using G
  · simpa [pattern, primitive_input, primitive_output, primitiveSignature, hole] using H

/-- Actual serial assembly, with no remaining skeleton edges. -/
@[reducible] def net {d I J K} (G : Hypernet d I J) (H : Hypernet d J K) : Hypernet d I K :=
  (pattern d I J K).expand (filling G H)

/-- A global primitive-label property is preserved by simultaneous edge expansion. -/
theorem allLabels_expand (P : Primitive → Prop) {d I O} (C : Hypernet d I O)
    (H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (free : ∀ e, AllLabels P (H e)) : AllLabels P (C.expand H) := by
  intro e
  exact free e.1 e.2

/-- Serial composition introduces no additional primitive labels. -/
theorem allLabels_net (P : Primitive → Prop) {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (g : AllLabels P G) (h : AllLabels P H) : AllLabels P (net G H) := by
  apply allLabels_expand
  intro b
  cases d <;> cases b <;> assumption

theorem focusFree_net {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (g : FocusFree G) (h : FocusFree H) : FocusFree (net G H) := allLabels_net _ g h

theorem holeFree_net {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (g : HoleFree G) (h : HoleFree H) : HoleFree (net G H) := allLabels_net _ g h

end Serial
end Hypernets.Copying

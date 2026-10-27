import Hypernets.Copying.SpliceBoundary

/-! External interface permutations transport actual combined-machine transitions.
They are realised by typed corolla contexts, not by an additional rewrite rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.InterfacePermutation
open Graph
namespace PlugContext
variable {d : Nat} (o : (alphabet d).Symbol)
    (p : TypedPermutation ((alphabet d).signature.output o))
    (G : Hypernet d ((alphabet d).signature.input o) ((alphabet d).signature.output o))

def context := net (Net.corolla (alphabet d).signature o) p

theorem insert (v : G.Vertex) :
    Port.map (Net.PlugUnit.leftVertices G).toFun
      (Net.Replacement.insert (context o p) (0 : Fin 1) G v) = (ports G p).toFun v := by
  cases v with
  | internal v => rfl
  | input i =>
    simp [Net.Replacement.insert,context,net,Net.sourcePort,Net.corolla,
      List.getElem_map,Net.Replacement.host,Port.map,ports]
  | output i =>
    simp [Net.Replacement.insert,context,net,Net.targetPort,Net.corolla,
      List.getElem_map,Net.Replacement.host,Port.map,ports]

/-- Removing a permuted corolla's hole gives exactly the interface-permuted net. -/
noncomputable def iso : DeepIso ((context o p).plug (0 : Fin 1) G) (net G p) := DeepIso.ofIso {
  vertices := Net.PlugUnit.leftVertices G
  edges := Net.PlugUnit.leftEdges G
  internal_label := by rintro (x | y); exact nomatch x; rfl
  edge_label := by rintro (x | y); exact False.elim (Net.PlugUnit.noEdge x); rfl
  source := by
    rintro (x | y)
    · exact False.elim (Net.PlugUnit.noEdge x)
    · change ((G.source y).map _).map _ = (G.source y).map _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => insert o p G v)
  target := by
    rintro (x | y)
    · exact False.elim (Net.PlugUnit.noEdge x)
    · change ((G.target y).map _).map _ = (G.target y).map _
      rw [List.map_map]
      exact List.map_congr_left (fun v _ => insert o p G v) }
end PlugContext

/-- Every existing compute rule transports, through the original context-closure
constructor. Stability and copyability premises stay inside the supplied step. -/
theorem rewrite {d I O} {G H : Hypernet d I O} {v w}
    (p : TypedPermutation O) (step : Combined.Rewrite G v H w) :
    Combined.Rewrite (net G p) ((ports G p).toFun v) (net H p) ((ports H p).toFun w) := by
  cases d with
  | zero =>
    have r := Combined.Rewrite.rename (PlugContext.iso (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p G)
      (PlugContext.iso (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p H)
      (Combined.Rewrite.plug (PlugContext.context (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) step)
    change Combined.Rewrite (net G p)
      (Port.map (Net.PlugUnit.leftVertices G).toFun (Net.Replacement.insert (PlugContext.context (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) G v))
      (net H p) (Port.map (Net.PlugUnit.leftVertices H).toFun (Net.Replacement.insert (PlugContext.context (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) H w)) at r
    rw [PlugContext.insert (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p G v,
      PlugContext.insert (primitiveLabel 0 (.hole ⟨0,I,O⟩)) p H w] at r
    exact r
  | succ d =>
    have r := Combined.Rewrite.rename (PlugContext.iso (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p G)
      (PlugContext.iso (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p H)
      (Combined.Rewrite.plug (PlugContext.context (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) step)
    change Combined.Rewrite (net G p)
      (Port.map (Net.PlugUnit.leftVertices G).toFun (Net.Replacement.insert (PlugContext.context (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) G v))
      (net H p) (Port.map (Net.PlugUnit.leftVertices H).toFun (Net.Replacement.insert (PlugContext.context (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p) (0 : Fin 1) H w)) at r
    rw [PlugContext.insert (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p G v,
      PlugContext.insert (primitiveLabel (d+1) (.hole ⟨0,I,O⟩)) p H w] at r
    exact r

/-- Keep the token mode and move its coordinate with the actual interface action. -/
def state {d I O} (p : TypedPermutation O) (s : Combined.State d I O) : Combined.State d I O :=
  ⟨net s.1 p,(s.2.1,(ports s.1 p).toFun s.2.2)⟩

theorem step {d I O} (p : TypedPermutation O) {s t : Combined.State d I O}
    (a : Combined.Step s t) : Combined.Step (state p s) (state p t) := by
  cases a with
  | search G a => exact .search _ ((Search.ofBoundaryIso (iso G p)).step a)
  | rewrite a => exact .rewrite (rewrite p a)

/-- No extra transitions are charged for changing external resource positions. -/
theorem run {d I O} (p : TypedPermutation O) {s t : Combined.State d I O} {n}
    (a : (Combined.machine d I O).Steps n s t) :
    (Combined.machine d I O).Steps n (state p s) (state p t) := by
  induction a with
  | zero => exact .zero _
  | cons a _ ih => exact .cons (step p a) ih

theorem final_iff {d I O} (p : TypedPermutation O) (s : Combined.State d I O) :
    (Combined.machine d I O).final (state p s) ↔ (Combined.machine d I O).final s := by
  change (s.2.1 = .backtrack ∧ ((ports s.1 p).toFun s.2.2).IsInput) ↔ _
  rw [input_iff]
  rfl
/-- Undoing the interface action restores a state up to recursive representation. -/
def roundtripState {d I O} (p : TypedPermutation O) (s : Combined.State d I O) :
    Combined.StateIso s (state p.symm (state p s)) where
  graph := roundtrip s.1 p
  mode := rfl
  vertex := by
    change Port.map (roundtrip s.1 p).vertices.toFun s.2.2 =
      (ports (net s.1 p) p.symm).toFun ((ports s.1 p).toFun s.2.2)
    cases s.2.2 with
    | internal v => rfl
    | input i => rfl
    | output i =>
      change Port.output i = Port.output (p.bijection.invFun (p.bijection.toFun i))
      rw [p.bijection.left_inv]

/-- Exact successful costs are invariant, in both directions, for the whole
combined machine. The reverse direction uses inverse permutation and StateIso. -/
theorem terminatesIn_iff {d I O} (p : TypedPermutation O) (s : Combined.State d I O) (n : Nat) :
    Combined.TerminatesIn n (state p s) ↔ Combined.TerminatesIn n s := by
  constructor
  · rintro ⟨t,a,done⟩
    apply (Combined.terminatesIn_iso (roundtripState p s) n).mpr
    exact ⟨state p.symm t,run p.symm a,(final_iff p.symm t).mpr done⟩
  · rintro ⟨t,a,done⟩
    exact ⟨state p t,run p a,(final_iff p t).mpr done⟩
end Hypernets.Copying.InterfacePermutation

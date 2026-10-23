import Hypernets.Graph.Hierarchy

/-!
Type-correct replacement at an arbitrary box depth. Sites select an occurrence,
not an edge label, so equal box bodies do not cause simultaneous replacement.
This module defines addressed replacement. DeepContext proves context closure
under hole-label freshness; DeepAssociativity proves nested substitution laws.
-/

namespace Hypernets.Graph.Net

universe u v

/-- Change labels individually, preserving the signature of each edge. -/
@[reducible] def relabelEdges {L : Type} {Op : Type u} {Op' : Type v}
    {σ : Signature L Op} {I O : List L} (G : Net σ I O) (τ : Signature L Op')
    (labels : G.Edge → Op')
    (input : ∀ e, τ.input (labels e) = σ.input (G.edgeLabel e))
    (output : ∀ e, τ.output (labels e) = σ.output (G.edgeLabel e)) : Net τ I O where
  Internal := G.Internal
  Edge := G.Edge
  finiteInternal := G.finiteInternal
  finiteEdge := G.finiteEdge
  internalLabel := G.internalLabel
  edgeLabel := labels
  source := G.source
  target := G.target
  source_nodup := G.source_nodup
  target_nodup := G.target_nodup
  source_unique := G.source_unique
  target_unique := G.target_unique
  source_coverage := G.source_coverage
  target_coverage := G.target_coverage
  source_typed e := (G.source_typed e).trans (input e).symm
  target_typed e := (G.target_typed e).trans (output e).symm

end Hypernets.Graph.Net

namespace Hypernets.Linear

open Graph

/-- Change the content of one specified box edge. External port types and
incidence remain unchanged because the binding/free-variable interface agrees. -/
@[reducible] noncomputable def replaceBox {Op : Type} {ops : Operations Op}
    {depth : Nat} {I O} (G : Hypernet ops (depth + 1) I O)
    (e : G.Edge) (b : Box (alphabet ops depth)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet ops depth [.term] (List.replicate (b.bound + b.free) .term)) :
    Hypernet ops (depth + 1) I O := by
  classical
  exact G.relabelEdges (alphabet ops (depth + 1)).signature
    (fun f => if f = e then Sum.inr (⟨b.bound, b.free, body⟩ : Box (alphabet ops depth))
      else G.edgeLabel f)
    (by
      intro f
      by_cases h : f = e
      · subst f; simp [alphabet, nextAlphabet, label]
      · simp [alphabet, nextAlphabet, h])
    (by
      intro f
      by_cases h : f = e
      · subst f; simp [alphabet, nextAlphabet, label]
      · simp [alphabet, nextAlphabet, h])

/-- An occurrence address carries the interface and the available depth bound
at the selected edge. A replacement with the wrong interface cannot be passed. -/
inductive Site {Op : Type} (ops : Operations Op) :
    {depth : Nat} → {I O : List Wire} → Hypernet ops depth I O →
      (localDepth : Nat) → List Wire → List Wire → Type 1 where
  | shallow {depth I O} (G : Hypernet ops depth I O) (e : G.Edge) :
      Site ops G depth ((alphabet ops depth).signature.input (G.edgeLabel e))
        ((alphabet ops depth).signature.output (G.edgeLabel e))
  | inside {depth I O} {G : Hypernet ops (depth + 1) I O}
      (e : G.Edge) (b : Box (alphabet ops depth)) (label : G.edgeLabel e = .inr b)
      {localDepth J K} (site : Site ops b.body localDepth J K) : Site ops G localDepth J K

/-- Shallow replacement changes the graph. Descending through a box changes
only that box's label and preserves every enclosing incidence structure. -/
noncomputable def plugAt {Op : Type} {ops : Operations Op}
    {depth : Nat} {I O} {G : Hypernet ops depth I O} {localDepth J K}
    (site : Site ops G localDepth J K) (H : Hypernet ops localDepth J K) :
    Hypernet ops depth I O :=
  match site with
  | .shallow C e => C.plug e H
  | .inside e b label inner => replaceBox _ e b label (plugAt inner H)

theorem plugAt_shallow {Op : Type} {ops : Operations Op} {depth I O}
    (G : Hypernet ops depth I O) (e : G.Edge)
    (H : Hypernet ops depth ((alphabet ops depth).signature.input (G.edgeLabel e))
      ((alphabet ops depth).signature.output (G.edgeLabel e))) :
    plugAt (.shallow G e) H = G.plug e H := rfl

/-- Concrete locality of deep replacement: all outer source lists are unchanged. -/
theorem plugAt_inside_source {Op : Type} {ops : Operations Op} {depth I O}
    (G : Hypernet ops (depth + 1) I O) (e : G.Edge) (b : Box (alphabet ops depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site ops b.body localDepth J K) (H : Hypernet ops localDepth J K) :
    (plugAt (Site.inside e b label site) H).source = G.source := rfl

theorem plugAt_inside_target {Op : Type} {ops : Operations Op} {depth I O}
    (G : Hypernet ops (depth + 1) I O) (e : G.Edge) (b : Box (alphabet ops depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site ops b.body localDepth J K) (H : Hypernet ops localDepth J K) :
    (plugAt (Site.inside e b label site) H).target = G.target := rfl

/-- Changing a box body changes no other outer edge label, even when that other
edge happened to carry exactly the same old box content. -/
theorem plugAt_inside_other_label {Op : Type} {ops : Operations Op} {depth I O}
    (G : Hypernet ops (depth + 1) I O) (e f : G.Edge) (b : Box (alphabet ops depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site ops b.body localDepth J K) (H : Hypernet ops localDepth J K) (ne : f ≠ e) :
    (plugAt (Site.inside e b label site) H).edgeLabel f = G.edgeLabel f := by
  simp [plugAt, replaceBox, ne]

end Hypernets.Linear

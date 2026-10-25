import Hypernets.Graph.DeepPlugging
import Hypernets.Copying.Hierarchy

/-! Addressed replacement for copying hypernets, with term/atom box interfaces. -/
namespace Hypernets.Copying

open Graph

/-- Change the content of one specified box edge. External port types and
incidence remain unchanged because the binding/free-variable interface agrees. -/
@[reducible] noncomputable def replaceBox
    {depth : Nat} {I O} (G : Hypernet (depth + 1) I O)
    (e : G.Edge) (b : Box (alphabet depth)) (label : G.edgeLabel e = .inr b)
    (body : Hypernet depth [.term] (environmentInterface (b.bound + b.freeVariables) b.freeAtoms)) :
    Hypernet (depth + 1) I O := by
  classical
  exact G.relabelEdges (alphabet (depth + 1)).signature
    (fun f => if f = e then Sum.inr (⟨b.bound, b.freeVariables, b.freeAtoms, body⟩ : Box (alphabet depth))
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
inductive Site :
    {depth : Nat} → {I O : List Wire} → Hypernet depth I O →
      (localDepth : Nat) → List Wire → List Wire → Type 1 where
  | shallow {depth I O} (G : Hypernet depth I O) (e : G.Edge) :
      Site G depth ((alphabet depth).signature.input (G.edgeLabel e))
        ((alphabet depth).signature.output (G.edgeLabel e))
  | inside {depth I O} {G : Hypernet (depth + 1) I O}
      (e : G.Edge) (b : Box (alphabet depth)) (label : G.edgeLabel e = .inr b)
      {localDepth J K} (site : Site b.body localDepth J K) : Site G localDepth J K

/-- Shallow replacement changes the graph. Descending through a box changes
only that box's label and preserves every enclosing incidence structure. -/
noncomputable def plugAt
    {depth : Nat} {I O} {G : Hypernet depth I O} {localDepth J K}
    (site : Site G localDepth J K) (H : Hypernet localDepth J K) :
    Hypernet depth I O :=
  match site with
  | .shallow C e => C.plug e H
  | .inside e b label inner => replaceBox _ e b label (plugAt inner H)

theorem plugAt_shallow {depth I O}
    (G : Hypernet depth I O) (e : G.Edge)
    (H : Hypernet depth ((alphabet depth).signature.input (G.edgeLabel e))
      ((alphabet depth).signature.output (G.edgeLabel e))) :
    plugAt (.shallow G e) H = G.plug e H := rfl

/-- Concrete locality of deep replacement: all outer source lists are unchanged. -/
theorem plugAt_inside_source {depth I O}
    (G : Hypernet (depth + 1) I O) (e : G.Edge) (b : Box (alphabet depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site b.body localDepth J K) (H : Hypernet localDepth J K) :
    (plugAt (Site.inside e b label site) H).source = G.source := rfl

theorem plugAt_inside_target {depth I O}
    (G : Hypernet (depth + 1) I O) (e : G.Edge) (b : Box (alphabet depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site b.body localDepth J K) (H : Hypernet localDepth J K) :
    (plugAt (Site.inside e b label site) H).target = G.target := rfl

/-- Changing a box body changes no other outer edge label, even when that other
edge happened to carry exactly the same old box content. -/
theorem plugAt_inside_other_label {depth I O}
    (G : Hypernet (depth + 1) I O) (e f : G.Edge) (b : Box (alphabet depth))
    (label : G.edgeLabel e = .inr b) {localDepth J K}
    (site : Site b.body localDepth J K) (H : Hypernet localDepth J K) (ne : f ≠ e) :
    (plugAt (Site.inside e b label site) H).edgeLabel f = G.edgeLabel f := by
  simp [plugAt, replaceBox, ne]

end Hypernets.Copying

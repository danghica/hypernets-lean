import Hypernets.Copying.ApplicationExamples

/-! The proved non-arithmetic copying rules, kept distinct from intrinsic search.
This is a concrete subsystem; arithmetic and the complete-UAM laws remain open. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph

/-- Actual local rule graphs and their active input coordinates. -/
inductive Local : {d : Nat} → {I O : List Wire} →
    (G : Hypernet d I O) → G.Vertex → (H : Hypernet d I O) → H.Vertex → Prop where
  | allocate {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
      Local (Allocation.before G) (.input 0) (Allocation.after G) (.input 0)
  | read {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
      Local (Dereference.before T d) (Dereference.inputPort h 0)
        (Dereference.after T d) (Dereference.inputPort h 0)
  | assign {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (stable : Stable G) :
      Local (Assignment.before T G) (Assignment.inputPort h O 0)
        (Assignment.after T G) (Assignment.inputPort h O 0)
  | same {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
      Local (AtomEquality.Same.before T d) (AtomEquality.Same.inputPort h 0)
        (AtomEquality.Same.after T d) (AtomEquality.Same.inputPort h 0)
  | different {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
      Local (AtomEquality.Different.before T U d) (AtomEquality.Different.inputPort n m 0)
        (AtomEquality.Different.after T U d) (AtomEquality.Different.inputPort n m 0)
  | beta {d k h O} (B : Hypernet d [.term] (environmentInterface (k+1) h))
      (G : Hypernet (d+1) [.term] O) (stable : Stable G) :
      Local (Application.before B G) (.input 0) (Application.after B G) (.input 0)
  | copy {d n k h} (T : ContractionTree .term (n+1))
      (G : Hypernet d [.term] (environmentInterface k h)) (copyable : Copyable G) :
      Local (CopyRule.before T G) (.input ⟨0,by simp⟩) (CopyRule.after T G) (.input ⟨0,by simp⟩)

/-- Match at the current outer level by typed insertion or simultaneous assembly.
There is no rule for evaluating inside a closed box. Recursive isomorphisms only
rename representations; they do not move the token into box bodies. -/
inductive Rewrite : {d : Nat} → {I O : List Wire} →
    (G : Hypernet d I O) → G.Vertex → (H : Hypernet d I O) → H.Vertex → Prop where
  | local {d I O G v H w} : @Local d I O G v H w → Rewrite G v H w
  | rename {d I O} {G H G' H' : Hypernet d I O} {v w}
      (f : DeepIso G G') (g : DeepIso H H') (step : Rewrite G v H w) :
      Rewrite G' (Port.map f.vertices.toFun v) H' (Port.map g.vertices.toFun w)
  | plug {d I O} (C : Hypernet d I O) (e : C.Edge)
      {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e))} {v w}
      (step : Rewrite G v H w) :
      Rewrite (C.plug e G) (Net.Replacement.insert C e G v)
        (C.plug e H) (Net.Replacement.insert C e H w)
  | expand {d I O} (C : Hypernet d I O)
      (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e)))
      (e : C.Edge) (others : ∀ b, b ≠ e → F b = K b) {v w}
      (step : Rewrite (F e) v (K e) w) :
      Rewrite (C.expand F) (Net.Expansion.insert C F e v)
        (C.expand K) (Net.Expansion.insert C K e w)

abbrev State (d : Nat) (I O : List Wire) := Σ G : Hypernet d I O, Search.Position G

/-- Search is still its existing incidence relation; every rewrite changes mode explicitly. -/
inductive Step {d I O} : State d I O → State d I O → Prop where
  | search (G : Hypernet d I O) {s t} : Search.Step G s t → Step ⟨G,s⟩ ⟨G,t⟩
  | rewrite {G H v w} : Rewrite G v H w → Step ⟨G,(.rewrite,v)⟩ ⟨H,(.search,w)⟩

theorem final_normal {d I O} {s : State d I O} (done : Search.Completed s.2) : ∀ t, ¬ Step s t := by
  intro t step; cases step with
  | @search G s t step =>
    rcases s with ⟨mode,v⟩
    rcases done with ⟨eq,input⟩
    change mode = .backtrack at eq
    subst mode
    exact Search.final_no_step input step
  | rewrite => cases done.1

def machine (d : Nat) (I O : List Wire) : Machine (State d I O) where
  step := Step
  final s := Search.Completed s.2
  final_normal h := final_normal h _

/-- Every local rule now performs a real graph-changing subsystem transition. -/
theorem local_step {d I O} {G H : Hypernet d I O} {v w} (step : Local G v H w) :
    Step ⟨G,(.rewrite,v)⟩ ⟨H,(.search,w)⟩ := .rewrite (.local step)

/-- No rewrite is smuggled into the old linear or the copying search relation. -/
theorem rewrite_not_search {d I O} {G : Hypernet d I O} (v : G.Vertex) {t} :
    ¬ Search.Step G (.rewrite,v) t := Search.no_rewrite
end Hypernets.Copying.Combined

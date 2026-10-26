import Hypernets.Copying.DereferenceExecution

/-! Ordered carrier renaming of the arbitrary matched tree preserves both rule sides. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph

/-- An isomorphism of primitive graphs lifts to the copying hierarchy at any allowance. -/
def liftIso {I O} {G H : Net primitiveSignature I O} (f : Net.RelIso Eq G H) (d : Nat) :
    DeepIso (G.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d))
      (H.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)) where
  vertices := f.vertices
  edges := f.edges
  internal_label := f.internal_label
  edge_label e := by
    change LabelEquiv d (primitiveLabel d (G.edgeLabel e)) (primitiveLabel d (H.edgeLabel (f.edges.toFun e)))
    rw [← f.edge_label e]; exact labelEquiv_refl d _
  source := f.source
  target := f.target

def beforeBaseIso {h} {T U : ContractionTree .atom (h+1)} (f : T.net.Iso U.net) :
    Net.RelIso Eq ((beforeFrame h).expand (beforeFill T)) ((beforeFrame h).expand (beforeFill U)) :=
  Net.ExpansionIso.iso (beforeFrame h) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _)

def afterBaseIso {h} {T U : ContractionTree .atom (h+1)} (f : T.net.Iso U.net) :
    Net.RelIso Eq ((afterFrame h).expand (afterFill T)) ((afterFrame h).expand (afterFill U)) :=
  Net.ExpansionIso.iso (afterFrame h) (fun e => by
    cases e
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.ofIso (fun _ => rfl) f
    · exact Net.RelIso.refl (fun _ => rfl) _
    · exact Net.RelIso.refl (fun _ => rfl) _)

/-- Rename the tree carrier without changing the reading instance or external ordering. -/
def before_rename {h} {T U : ContractionTree .atom (h+1)} (f : T.net.Iso U.net) (d : Nat) :
    DeepIso (before T d) (before U d) := liftIso (beforeBaseIso f) d

def after_rename {h} {T U : ContractionTree .atom (h+1)} (f : T.net.Iso U.net) (d : Nat) :
    DeepIso (after T d) (after U d) := liftIso (afterBaseIso f) d

/-- Renaming preserves the identity of the designated store occurrence. -/
theorem rename_store {h} {T U : ContractionTree .atom (h+1)} (f : T.net.Iso U.net) (d : Nat) :
    (before_rename f d).edges.toFun (beforeStore T d) = beforeStore U d ∧
    (after_rename f d).edges.toFun (afterStore T d) = afterStore U d := ⟨rfl,rfl⟩

/-- Arbitrarily padded local pairs remain actual dereference rules. -/
theorem rule_pad {d h} {L R : Hypernet d (inputs h) [.term]} (s : Rule L R) (n : Nat) :
    Rule (Translation.pad d n L) (Translation.pad d n R) := by
  induction n with
  | zero => exact s
  | succ n ih => exact rule_raise ih
end Hypernets.Copying.Dereference

import Hypernets.Copying.SearchTyping

/-! Search's actual one-step and finite-run padding invariance. These results
are proved for the concrete search rules, not inferred from determinism. -/
namespace Hypernets.Copying.Search
open Graph

/-- One original allowance increase satisfies every search transport law. -/
def padding (d : Nat) {I O} (G : Hypernet d I O) : Transport G (raise d G) := by
  cases d with
  | zero =>
    exact {
      ports := Bijection.refl _
      edges := Bijection.refl _
      primitive := by intro e p; cases h : G.edgeLabel e; simp [raise,Net.relabel,primitiveLabel,Bijection.refl,h] <;> constructor <;> intro eq <;> cases eq <;> rfl
      source := by intro e; simp [raise,Net.relabel,Bijection.refl]
      target := by intro e; simp [raise,Net.relabel,Bijection.refl]
      input_iff := fun _ => Iff.rfl }
  | succ d =>
    exact {
      ports := Bijection.refl _
      edges := Bijection.refl _
      primitive := by intro e p; cases h : G.edgeLabel e <;> simp [raise,Net.relabel,primitiveLabel,Bijection.refl,h] <;> constructor <;> intro eq <;> cases eq <;> rfl
      source := by intro e; simp [raise,Net.relabel,Bijection.refl]
      target := by intro e; simp [raise,Net.relabel,Bijection.refl]
      input_iff := fun _ => Iff.rfl }

namespace Transport

def refl {d I O} (G : Hypernet d I O) : Transport G G where
  ports := Bijection.refl _
  edges := Bijection.refl _
  primitive _ _ := Iff.rfl
  source _ := by simp [Bijection.refl]
  target _ := by simp [Bijection.refl]
  input_iff _ := Iff.rfl

def trans {d r q I O J K U V} {G : Hypernet d I O} {H : Hypernet r J K} {F : Hypernet q U V}
    (f : Transport G H) (g : Transport H F) : Transport G F where
  ports := f.ports.trans g.ports
  edges := f.edges.trans g.edges
  primitive e p := (f.primitive e p).trans (g.primitive _ p)
  source e := by
    change (G.source e).map (g.ports.toFun ∘ f.ports.toFun) = _
    rw [← List.map_map,f.source,g.source]; rfl
  target e := by
    change (G.target e).map (g.ports.toFun ∘ f.ports.toFun) = _
    rw [← List.map_map,f.target,g.target]; rfl
  input_iff v := (g.input_iff _).trans (f.input_iff v)
end Transport

/-- Iteration adds no interaction or finite search trace. -/
def pad {d I O} (G : Hypernet d I O) : (n : Nat) → Transport G (Translation.pad d n G)
  | 0 => Transport.refl G
  | n+1 => (pad G n).trans (padding _ _)

def castDepth {d r I O} (eq : d = r) (G : Hypernet d I O) : Transport G (Translation.castDepth eq G) := by
  cases eq; exact Transport.refl G

def padTo {d I O} (G : Hypernet d I O) (n : Nat) (bound : d ≤ n) : Transport G (Translation.padTo n bound G) :=
  (pad G (n-d)).trans (castDepth (Nat.add_sub_of_le bound) _)

theorem padding_step_iff {d I O} (G : Hypernet d I O) (s t : Position G) :
    Step (raise d G) ((padding d G).positions.toFun s) ((padding d G).positions.toFun t) ↔ Step G s t :=
  (padding d G).step_iff s t

theorem padTo_trace_iff {d I O} (G : Hypernet d I O) (N : Nat) (bound : d ≤ N)
    (s t : Position G) (n : Nat) :
    Trace (Step (Translation.padTo N bound G)) ((padTo G N bound).positions.toFun s)
      ((padTo G N bound).positions.toFun t) n ↔ Trace (Step G) s t n :=
  (padTo G N bound).trace_iff s t n
end Hypernets.Copying.Search

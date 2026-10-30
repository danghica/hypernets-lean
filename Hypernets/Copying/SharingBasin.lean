import Hypernets.Copying.SharingTreeExpansion
import Hypernets.Graph.PredecessorBasin
import Hypernets.Copying.OpeningOccurrence

/-! A maximal sharing component of an arbitrary host is a literal sharing-tree
context, with its old holes and ordered boundary attachments preserved. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Opening

/-- Sharing primitives and same-sort, one-output tree holes. -/
def SharingLabel (d : Nat) (s : ShareSort) (a : (alphabet d).Symbol) : Prop :=
  a = primitiveLabel d (.weakening s) ∨ a = primitiveLabel d (.contraction s) ∨
    ∃ h n, a = primitiveLabel d (.hole h) ∧
      h.input = List.replicate n s.wire ∧ h.output = [s.wire]

namespace SharingLabel
variable {d s a}

theorem target (sharing : SharingLabel d s a) : (alphabet d).signature.output a = [s.wire] := by
  rcases sharing with rfl | rfl | ⟨h,n,rfl,input,output⟩
  · exact primitive_output d _
  · exact primitive_output d _
  · rw [primitive_output]; exact output

theorem input (sharing : SharingLabel d s a) :
    ∃ n, (alphabet d).signature.input a = List.replicate n s.wire := by
  rcases sharing with rfl | rfl | ⟨h,n,rfl,input,output⟩
  · exact ⟨0,primitive_input d _⟩
  · exact ⟨2,primitive_input d _⟩
  · exact ⟨n,(primitive_input d _).trans input⟩
end SharingLabel

namespace SharingBasin
variable {d I O} (G : Hypernet d I O) (s : ShareSort)

def Eligible (e : G.Edge) : Prop := SharingLabel d s (G.edgeLabel e)

theorem single (e : G.Edge) (sharing : Eligible G s e) : (G.target e).length = 1 := by
  rw [G.target_length,SharingLabel.target sharing]; rfl

theorem source_label (e : G.Edge) (sharing : Eligible G s e) (v : G.Vertex)
    (mem : v ∈ G.source e) : G.vertexLabel v = s.wire := by
  have typed := List.mem_map_of_mem (f := G.vertexLabel) mem
  change _ ∈ (G.source e).map (Port.label G.internalLabel) at typed
  rw [G.source_typed] at typed
  obtain ⟨n,input⟩ := SharingLabel.input sharing
  rw [input] at typed
  exact (List.mem_replicate.mp typed).2

theorem target_label (e : G.Edge) (sharing : Eligible G s e) (v : G.Vertex)
    (mem : v ∈ G.target e) : G.vertexLabel v = s.wire := by
  have typed := List.mem_map_of_mem (f := G.vertexLabel) mem
  change _ ∈ (G.target e).map (Port.label G.internalLabel) at typed
  rw [G.target_typed,SharingLabel.target sharing] at typed
  simpa using typed

/-- The actual host supplies the maximal component whenever its chosen sharing
root exits into a nonsharing edge (or into the host's external output). -/
def basin (root : G.Edge) (output : G.Vertex) (sharing : Eligible G s root)
    (target : G.target root = [output])
    (terminal : ∀ e, Eligible G s e → ¬ G.Adjacent root e) : G.RootedBasin s.wire :=
  G.predecessorBasin (Eligible G s) root s.wire output sharing target
    (single G s) terminal (source_label G s) (target_label G s)

variable {G s} (S : G.RootedBasin s.wire)
    (labels : ∀ e, S.chosen e → Eligible G s e)
    (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)

/-- Normalize the selected component without discarding any original hole. -/
noncomputable def context : SharingTreeContext s inputs.length d where
  net := (S.setNet inputs distinct boundary).toNet
  labels e := labels e.val e.property
  acyclic := S.acyclic inputs distinct boundary

/-- Full-label occurrence of the computed sharing context in the original host. -/
noncomputable def occurrence : Occurrence (context S labels inputs distinct boundary).net G :=
  (show MatchEmbedding (context S labels inputs distinct boundary).net G from {
    ports := S.ports inputs distinct boundary
    edges := Subtype.val
    edge_injective := fun _ _ h => Subtype.ext h
    primitive := fun _ _ h => h
    source := S.source_ports inputs distinct boundary
    target := S.target_ports inputs distinct boundary
  }).occurrence (fun _ => labelEquiv_refl _ _)

theorem occurrence_input (i : Fin (List.replicate inputs.length s.wire).length) :
    (occurrence S labels inputs distinct boundary).ports (.input i) =
      (inputs.get ⟨i.val,by simpa using i.isLt⟩).val := rfl

theorem occurrence_output : (occurrence S labels inputs distinct boundary).ports (.output 0) = S.output := rfl

end SharingBasin
end Hypernets.Copying

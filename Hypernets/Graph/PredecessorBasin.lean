import Hypernets.Graph.RootedBasinSelection

/-! The maximal predecessor component consists of all sharing-like edges
whose forward sharing path reaches a specified terminal root. -/
namespace Hypernets.Graph.Net
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}
    (G : Net σ I O) (P : G.Edge → Prop) (root : G.Edge)

def SharingNext (e f : G.Edge) : Prop := P e ∧ G.Adjacent e f ∧ P f

def PredecessorOf (e : G.Edge) : Prop := P e ∧ ∃ n, Trace (G.SharingNext P) e root n

/-- Every eligible immediate predecessor of a selected edge is selected. -/
theorem predecessor_closed {e f} (pe : P e) (adj : G.Adjacent e f)
    (chosen : G.PredecessorOf P root f) : G.PredecessorOf P root e := by
  obtain ⟨pf,n,path⟩ := chosen
  exact ⟨pe,n+1,.step ⟨pe,adj,pf⟩ path⟩

/-- The entire trace stays in the maximal predecessor component. -/
theorem predecessor_trace {e n} (pe : P e) (path : Trace (G.SharingNext P) e root n) :
    Trace (fun a b => G.PredecessorOf P root a ∧ G.Adjacent a b ∧ G.PredecessorOf P root b) e root n := by
  induction path with
  | refl => exact .refl _
  | @step a b c n edge tail ih =>
    exact .step ⟨⟨pe,n+1,.step edge tail⟩,edge.2.1,⟨edge.2.2,n,tail⟩⟩ (ih edge.2.2)

/-- Selecting all eligible ancestors of a terminal sharing root constructs
an actual finite converging component, including every unused sharing branch. -/
def predecessorBasin (sort : L) (output : G.Vertex) (pr : P root)
    (target : G.target root = [output])
    (single : ∀ e, P e → (G.target e).length = 1)
    (stop : ∀ f, P f → ¬ G.Adjacent root f)
    (sources : ∀ e, P e → ∀ v, v ∈ G.source e → G.vertexLabel v = sort)
    (targets : ∀ e, P e → ∀ v, v ∈ G.target e → G.vertexLabel v = sort) :
    G.RootedBasin sort where
  chosen := G.PredecessorOf P root
  root := root
  output := output
  root_chosen := ⟨pr,0,.refl root⟩
  root_target := target
  single e chosen := single e chosen.1
  reaches e chosen := by
    obtain ⟨pe,n,path⟩ := chosen
    exact ⟨n,G.predecessor_trace P root pe path⟩
  terminal f chosen := stop f chosen.1
  source_label e chosen := sources e chosen.1
  target_label e chosen := targets e chosen.1

end Hypernets.Graph.Net

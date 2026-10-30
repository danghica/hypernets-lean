import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Graph.Parallel

/-! Disjoint actual graph occurrences assemble in parallel, retaining the
original ordered boundary. This supports separating BPullW's unused copy row
from the unchanged part of the copying reduct. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence.ParallelJoin
open Graph
variable {d : Nat} {A : Type} {I O : A → List Wire} {J K X Y : List Wire}
    (F : ∀ a, Hypernet d (I a) (O a)) (B : Net.Parallel.Boundary I O J K)
    (finite : Enumeration A) {G : Hypernet d X Y} (f : ∀ a, Occurrence (F a) G)

/-- Every original component has its literal complete occurrence in parallel
assembly, including the prescribed ordered boundary maps. -/
def component (a : A) : Occurrence (F a) (Net.Parallel.net F B finite) where
  ports := Net.Parallel.embed F B a
  internals v := ⟨a,v⟩
  edges e := ⟨a,e⟩
  internal_map _ := rfl
  internal_injective := by intro v w eq; exact eq_of_heq (Sigma.mk.inj eq).2
  edge_injective := by intro v w eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

def ports : (Net.Parallel.net F B finite).Vertex → G.Vertex
  | .internal ⟨a,v⟩ => (f a).ports (.internal v)
  | .input i => let p := B.inputs.invFun i; (f p.1).ports (.input p.2)
  | .output i => let p := B.outputs.invFun i; (f p.1).ports (.output p.2)

theorem embed_ports (a : A) (v : (F a).Vertex) :
    ports F B finite f (Net.Parallel.embed F B a v) = (f a).ports v := by
  cases v with
  | internal _ => rfl
  | input i =>
    change (let p := B.inputs.invFun (B.inputs.toFun ⟨a,i⟩); (f p.1).ports (.input p.2)) = _
    rw [B.inputs.left_inv]
  | output i =>
    change (let p := B.outputs.invFun (B.outputs.toFun ⟨a,i⟩); (f p.1).ports (.output p.2)) = _
    rw [B.outputs.left_inv]

variable (disjoint : ∀ a b, a ≠ b → ∀ e c, (f a).edges e ≠ (f b).edges c)

def embedding : MatchEmbedding (Net.Parallel.net F B finite) G where
  ports := ports F B finite f
  edges e := (f e.1).edges e.2
  edge_injective := by
    rintro ⟨a,e⟩ ⟨b,c⟩ eq
    by_cases same : a = b
    · subst b
      exact congrArg (Sigma.mk a) ((f a).edge_injective eq)
    · exact False.elim (disjoint a b same e c eq)
  primitive e p label := (f e.1).matchEmbedding.primitive e.2 p label
  source e := by
    change (((F e.1).source e.2).map _).map _ = _
    rw [List.map_map,← (f e.1).source]
    exact List.map_congr_left (fun v _ => embed_ports F B finite f e.1 v)
  target e := by
    change (((F e.1).target e.2).map _).map _ = _
    rw [List.map_map,← (f e.1).target]
    exact List.map_congr_left (fun v _ => embed_ports F B finite f e.1 v)

/-- Parallel assembly requires no new freshness premise on vertices: complete
incidence and edge disjointness already imply the necessary injectivity. -/
noncomputable def occurrence : Occurrence (Net.Parallel.net F B finite) G :=
  (embedding F B finite f disjoint).occurrence (fun e => (f e.1).label e.2)

theorem occurrence_embed (a : A) (v : (F a).Vertex) :
    (occurrence F B finite f disjoint).ports (Net.Parallel.embed F B a v) = (f a).ports v :=
  embed_ports F B finite f a v

end Hypernets.Copying.Opening.Occurrence.ParallelJoin

import Hypernets.Copying.LocalRewriteOccurrence

/-! Complete occurrences of simultaneously filled components assemble when
their actual ordered ports agree with one shared frame. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence.ExpansionJoin
open Graph
variable {d I O X Y} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    {G : Hypernet d X Y} (f : ∀ e, Occurrence (F e) G)
    (host : C.Vertex → G.Vertex)

/-- The shared old-frame coordinates and local internal occurrences determine
all vertices of the assembled occurrence. -/
def ports : (C.expand F).Vertex → G.Vertex
  | .input i => host (.input i)
  | .output i => host (.output i)
  | .internal (.inl a) => host (.internal a)
  | .internal (.inr ⟨e,a⟩) => (f e).ports (.internal a)

def edges (e : (C.expand F).Edge) : G.Edge := (f e.1).edges e.2

theorem host_ports (v : C.Vertex) :
    ports C F f host (Net.Expansion.host C F v) = host v := by cases v <;> rfl

variable (input : ∀ e i, (f e).ports (.input i) = host (C.sourcePort e i))
    (output : ∀ e i, (f e).ports (.output i) = host (C.targetPort e i))
include input output

theorem insert_ports (e : C.Edge) (v : (F e).Vertex) :
    ports C F f host (Net.Expansion.insert C F e v) = (f e).ports v := by
  cases v with
  | input i => exact (host_ports C F f host (C.sourcePort e i)).trans (input e i).symm
  | output i => exact (host_ports C F f host (C.targetPort e i)).trans (output e i).symm
  | internal a => rfl

variable (disjoint : ∀ e a, e ≠ a → ∀ b c, (f e).edges b ≠ (f a).edges c)

/-- Full actual incidence determines a complete embedding; no additional
internal freshness or injectivity premise is needed. -/
noncomputable def embedding : MatchEmbedding (C.expand F) G where
  ports := ports C F f host
  edges := edges C F f
  edge_injective := by
    rintro ⟨e,b⟩ ⟨a,c⟩ eq
    by_cases same : e = a
    · subst a
      exact congrArg (Sigma.mk e) ((f e).edge_injective eq)
    · exact False.elim (disjoint e a same b c eq)
  primitive := fun ⟨e,b⟩ p h => (f e).matchEmbedding.primitive b p h
  source := by
    rintro ⟨e,b⟩
    change (((F e).source b).map (Net.Expansion.insert C F e)).map (ports C F f host) = G.source ((f e).edges b)
    rw [List.map_map,← (f e).source b]
    exact List.map_congr_left (fun v _ => insert_ports C F f host input output e v)
  target := by
    rintro ⟨e,b⟩
    change (((F e).target b).map (Net.Expansion.insert C F e)).map (ports C F f host) = G.target ((f e).edges b)
    rw [List.map_map,← (f e).target b]
    exact List.map_congr_left (fun v _ => insert_ports C F f host input output e v)

/-- Assemble the complete original-label occurrence of the expanded frame. -/
noncomputable def occurrence : Occurrence (C.expand F) G :=
  (embedding C F f host input output disjoint).occurrence (fun ⟨e,b⟩ => (f e).label b)

theorem occurrence_host (v : C.Vertex) :
    (occurrence C F f host input output disjoint).ports (Net.Expansion.host C F v) = host v :=
  host_ports C F f host v

theorem occurrence_insert (e : C.Edge) (v : (F e).Vertex) :
    (occurrence C F f host input output disjoint).ports (Net.Expansion.insert C F e v) = (f e).ports v :=
  insert_ports C F f host input output e v

end Hypernets.Copying.Opening.Occurrence.ExpansionJoin

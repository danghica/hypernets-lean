import Hypernets.Copying.MatchEmbedding
import Hypernets.Copying.DeepFillings

/-! Reflect and transfer an actual outer rule footprint whose edges avoid
shallow template holes. Unrelated replacements may have arbitrary outer
vertices and edges: only the matched incidences are reflected to the host. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Search.Expansion

theorem DeepFillingEdge.retained_of_not_hole {T d I O} {C : Hypernet d I O} {L R e}
    (cert : DeepFillingEdge T C L R e)
    (avoid : ∀ h, C.edgeLabel e ≠ primitiveLabel d (.hole h)) :
    Nonempty (Retained C L e × Retained C R e) := by
  rcases cert.origin with retained | ⟨h,label,rel⟩
  · obtain ⟨⟨l⟩,⟨r⟩⟩ := retained; exact ⟨l,r⟩
  · exact False.elim (avoid h label)

namespace RetainedFootprint
variable {d I O} (C : Hypernet d I O)
    {L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand L))

/-- The exclusion concerns each edge in this actual match, not every edge of
the filled graph. Deep boxed changes are permitted. -/
def AvoidsShallow : Prop := ∀ a h, C.edgeLabel (f.edges a).1 ≠ primitiveLabel d (.hole h)

variable {T : PreTemplate} (cert : ∀ e, DeepFillingEdge T C L R e)
    (avoid : AvoidsShallow C f)

noncomputable def left (e : A.Edge) : Retained C L (f.edges e).1 :=
  (Classical.choice ((cert _).retained_of_not_hole (avoid e))).1

noncomputable def right (e : A.Edge) : Retained C R (f.edges e).1 :=
  (Classical.choice ((cert _).retained_of_not_hole (avoid e))).2

include cert avoid

theorem source (e : A.Edge) :
    (C.expand L).source (f.edges e) = (C.source (f.edges e).1).map (Net.Expansion.host C L) := by
  have eq : f.edges e = ⟨(f.edges e).1,(left C f cert avoid e).edge⟩ :=
    congrArg (Sigma.mk (f.edges e).1) ((left C f cert avoid e).only (f.edges e).2)
  conv => lhs; rw [eq]
  exact (left C f cert avoid e).source_eq

theorem target (e : A.Edge) :
    (C.expand L).target (f.edges e) = (C.target (f.edges e).1).map (Net.Expansion.host C L) := by
  have eq : f.edges e = ⟨(f.edges e).1,(left C f cert avoid e).edge⟩ :=
    congrArg (Sigma.mk (f.edges e).1) ((left C f cert avoid e).only (f.edges e).2)
  conv => lhs; rw [eq]
  exact (left C f cert avoid e).target_eq

/-- Incidence coverage places every matched port at a genuine host coordinate.
No global inverse map exists for unrelated multi-edge shallow fillings. -/
theorem port_origin (v : A.Vertex) :
    ∃ x : C.Vertex, Net.Expansion.host C L x = f.ports v := by
  classical
  by_cases out : v.IsOutput
  · have notInput : ¬ v.IsInput := by cases v <;> simp_all [Port.IsInput,Port.IsOutput]
    obtain ⟨e,mem⟩ := (A.target_coverage v).mpr notInput
    have member := f.target_mem mem
    rw [target C f cert avoid e] at member
    obtain ⟨x,_,eq⟩ := List.mem_map.mp member
    exact ⟨x,eq⟩
  · obtain ⟨e,mem⟩ := (A.source_coverage v).mpr out
    have member := f.source_mem mem
    rw [source C f cert avoid e] at member
    obtain ⟨x,_,eq⟩ := List.mem_map.mp member
    exact ⟨x,eq⟩

noncomputable def port (v : A.Vertex) : C.Vertex :=
  Classical.choose (port_origin C f cert avoid v)

theorem host_port (v : A.Vertex) :
    Net.Expansion.host C L (port C f cert avoid v) = f.ports v :=
  Classical.choose_spec (port_origin C f cert avoid v)

theorem owner_injective : Function.Injective (fun e => (f.edges e).1) := by
  intro a b eq
  apply f.edge_injective
  have same {x y : (C.expand L).Edge} (r : Retained C L x.1) (eq : x.1 = y.1) : x = y := by
    obtain ⟨e,x⟩ := x
    obtain ⟨g,y⟩ := y
    dsimp at eq
    subst g
    exact congrArg (Sigma.mk e) ((r.only x).trans (r.only y).symm)
  exact same (left C f cert avoid a) eq

/-- Ordered reflection of the whole matched footprint, including boxed edges.
The MatchEmbedding interface retains exactly the primitive labels inspected by
local matching, together with every ordered incidence. -/
noncomputable def reflect : MatchEmbedding A C where
  ports := port C f cert avoid
  edges e := (f.edges e).1
  edge_injective := owner_injective C f cert avoid
  primitive e p label := by
    apply ((left C f cert avoid e).primitive p).mp
    have label := f.primitive e p label
    change (L (f.edges e).1).edgeLabel (f.edges e).2 = _ at label
    rwa [(left C f cert avoid e).only (f.edges e).2] at label
  source e := by
    apply (List.map_inj_right (f := Net.Expansion.host C L)
      (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [List.map_map]
    simp only [Function.comp_def,host_port]
    rw [f.source]
    exact source C f cert avoid e
  target e := by
    apply (List.map_inj_right (f := Net.Expansion.host C L)
      (fun _ _ eq => Net.Expansion.host_injective C L eq)).mp
    rw [List.map_map]
    simp only [Function.comp_def,host_port]
    rw [f.target]
    exact target C f cert avoid e

/-- Construct the other-side occurrence from the original retained corollas,
preserving every argument position and every possible boundary alias. -/
noncomputable def across : MatchEmbedding A (C.expand R) where
  ports := Net.Expansion.host C R ∘ (reflect C f cert avoid).ports
  edges e := ⟨(f.edges e).1,(right C f cert avoid e).edge⟩
  edge_injective := by
    intro e x eq
    exact owner_injective C f cert avoid (congrArg (fun z : (C.expand R).Edge => z.1) eq)
  primitive e p label := ((right C f cert avoid e).primitive p).mpr
    ((reflect C f cert avoid).primitive e p label)
  source e := by
    rw [← List.map_map,(reflect C f cert avoid).source]
    exact (right C f cert avoid e).source_eq.symm
  target e := by
    rw [← List.map_map,(reflect C f cert avoid).target]
    exact (right C f cert avoid e).target_eq.symm

/-- In particular the transferred match uses the actual paired specimen token. -/
theorem across_host {v : A.Vertex} {x : C.Vertex}
    (attached : f.ports v = Net.Expansion.host C L x) :
    (across C f cert avoid).ports v = Net.Expansion.host C R x := by
  have eq := Net.Expansion.host_injective C L ((host_port C f cert avoid v).trans attached)
  exact congrArg (Net.Expansion.host C R) eq

end RetainedFootprint
end Hypernets.Copying

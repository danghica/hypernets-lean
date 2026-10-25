import Hypernets.Copying.BindingFree

/-! Equivalence with the paper's positive vertex-to-vertex path formulation. -/
namespace Hypernets.Copying
open Graph

def BindingPathStep {d I O} (G : Hypernet d I O) (v w : G.Vertex) : Prop :=
  ∃ e, v ∈ G.source e ∧ w ∈ G.target e

namespace BindingFree

theorem ancestor_vertex_trace {d I O} {G : Hypernet d I O} {e f : G.Edge}
    (p : Ancestor G e f) {v : G.Vertex} (src : v ∈ G.source e) :
    ∃ w n, w ∈ G.source f ∧ Trace (BindingPathStep G) v w n := by
  induction p generalizing v with
  | refl => exact ⟨v,0,src,.refl v⟩
  | @step e g f a p ih =>
    obtain ⟨u,tgt,gs⟩ := a
    obtain ⟨w,n,fs,q⟩ := ih gs
    exact ⟨w,n+1,fs,.step ⟨e,src,tgt⟩ q⟩

theorem target_trace_strict {d I O} {G : Hypernet d I O} {v w : G.Vertex} {n}
    (p : Trace (BindingPathStep G) v w n) {e f : G.Edge}
    (tgt : v ∈ G.target e) (src : w ∈ G.source f) : StrictAncestor G e f := by
  induction p generalizing e f with
  | refl v => exact ⟨f,⟨v,tgt,src⟩,.refl f⟩
  | @step v u w n a p ih =>
    obtain ⟨g,gs,gt⟩ := a
    obtain ⟨z,gz,q⟩ := ih gt src
    exact ⟨g,⟨v,tgt,gs⟩,.step gz q⟩

/-- Positive edge ancestry with a source witness is exactly a nonempty path
from a source of the first edge to a source of the last edge. Source uniqueness
identifies the first edge of the vertex trace; reflexive reachability is excluded. -/
theorem strict_iff_vertex_path {d I O} (G : Hypernet d I O) (e f : G.Edge) :
    ((∃ v, v ∈ G.source e) ∧ StrictAncestor G e f) ↔
    ∃ v w n, v ∈ G.source e ∧ w ∈ G.source f ∧
      Trace (BindingPathStep G) v w (n+1) := by
  constructor
  · rintro ⟨⟨v,vs⟩,g,⟨u,ut,us⟩,p⟩
    obtain ⟨w,n,ws,q⟩ := ancestor_vertex_trace p us
    exact ⟨v,w,n,vs,ws,.step ⟨e,vs,ut⟩ q⟩
  · rintro ⟨v,w,n,vs,ws,p⟩
    cases p with
    | step a q =>
      obtain ⟨g,gs,gt⟩ := a
      have eq := G.source_unique vs gs
      subst g
      exact ⟨⟨v,vs⟩,target_trace_strict q gt ws⟩

end BindingFree
end Hypernets.Copying

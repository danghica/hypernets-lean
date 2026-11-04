import Hypernets.Copying.PropositionResultGraphs

/-! Exhaustive finite certificates for representation changes in the original
constant-result translation. Every map, inverse and ordered port is checked
by the Lean kernel; the tables are not trusted graph-matching results. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Result
open Graph

namespace ConstantBody
private abbrev source := Translation.constant 0 1 0 (.nat 1)
private abbrev target := Parametricity.oneBody 0
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal := FiniteGraphCertificate.emptyBijection source.finiteInternal target.finiteInternal rfl rfl
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[1],target.finiteEdge.elements[0]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[1],source.finiteEdge.elements[0]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end ConstantBody

namespace SharingFactorization
private abbrev source := mixed
private abbrev target := schematic sharing
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[5],target.finiteInternal.elements[6],target.finiteInternal.elements[0],target.finiteInternal.elements[1],target.finiteInternal.elements[2],target.finiteInternal.elements[7],target.finiteInternal.elements[8],target.finiteInternal.elements[3],target.finiteInternal.elements[4],target.finiteInternal.elements[9],target.finiteInternal.elements[10],target.finiteInternal.elements[11],target.finiteInternal.elements[12],target.finiteInternal.elements[13]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[2],source.finiteInternal.elements[3],source.finiteInternal.elements[4],source.finiteInternal.elements[7],source.finiteInternal.elements[8],source.finiteInternal.elements[0],source.finiteInternal.elements[1],source.finiteInternal.elements[5],source.finiteInternal.elements[6],source.finiteInternal.elements[9],source.finiteInternal.elements[10],source.finiteInternal.elements[11],source.finiteInternal.elements[12],source.finiteInternal.elements[13]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[4],target.finiteEdge.elements[3],target.finiteEdge.elements[5],target.finiteEdge.elements[6],target.finiteEdge.elements[7],target.finiteEdge.elements[14],target.finiteEdge.elements[8],target.finiteEdge.elements[9],target.finiteEdge.elements[10],target.finiteEdge.elements[11],target.finiteEdge.elements[12],target.finiteEdge.elements[13]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[4],source.finiteEdge.elements[3],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[9],source.finiteEdge.elements[10],source.finiteEdge.elements[11],source.finiteEdge.elements[12],source.finiteEdge.elements[13],source.finiteEdge.elements[14],source.finiteEdge.elements[8]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8],source.finiteEdge.elements[9],source.finiteEdge.elements[10],source.finiteEdge.elements[11],source.finiteEdge.elements[12],source.finiteEdge.elements[13],source.finiteEdge.elements[14]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end SharingFactorization


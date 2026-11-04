import Hypernets.Copying.PropositionSourceGraphs
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Source
open Graph

namespace ReadFactor
private abbrev source := Translation.term readTerm
private abbrev target := readFactored
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[0],target.finiteInternal.elements[2],target.finiteInternal.elements[5],target.finiteInternal.elements[4],target.finiteInternal.elements[6],target.finiteInternal.elements[1],target.finiteInternal.elements[3],target.finiteInternal.elements[7]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[0],source.finiteInternal.elements[5],source.finiteInternal.elements[1],source.finiteInternal.elements[6],source.finiteInternal.elements[3],source.finiteInternal.elements[2],source.finiteInternal.elements[4],source.finiteInternal.elements[7]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[6],target.finiteEdge.elements[0],target.finiteEdge.elements[3],target.finiteEdge.elements[7],target.finiteEdge.elements[8],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[4],target.finiteEdge.elements[5],target.finiteEdge.elements[9],target.finiteEdge.elements[10]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[1],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[2],source.finiteEdge.elements[7],source.finiteEdge.elements[8],source.finiteEdge.elements[0],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[9],source.finiteEdge.elements[10]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8],source.finiteEdge.elements[9],source.finiteEdge.elements[10]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end ReadFactor

namespace ReadUnused
private abbrev source := readReduced
private abbrev target := beforeX readUsed
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[1],target.finiteInternal.elements[0]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[1],target.finiteEdge.elements[4],target.finiteEdge.elements[0],target.finiteEdge.elements[2],target.finiteEdge.elements[3]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[2],source.finiteEdge.elements[0],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[1]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end ReadUnused

namespace SmallPull
private abbrev source := pullRight (Parametricity.readBody 0)
private abbrev target := contractBox (beforeX (Parametricity.readBody 0))
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[0],target.finiteInternal.elements[1]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end SmallPull

namespace LargePull
private abbrev source := pullRight (Parametricity.callReadBody 0)
private abbrev target := contractBox (beforeX (Parametricity.callReadBody 0))
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[0],target.finiteInternal.elements[1]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end LargePull

namespace SmallUse
private abbrev source := Serial.net (outsideWeak (Parametricity.readBody 0)) (primitiveNet 1 (.contraction .term))
private abbrev target := Serial.net (Parametricity.smallLeft 0) (use 1)
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[0],target.finiteInternal.elements[1]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[3]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end SmallUse

namespace LargeUse
private abbrev source := Serial.net (outsideWeak (Parametricity.callReadBody 0)) (primitiveNet 2 (.contraction .term))
private abbrev target := Serial.net (Parametricity.largeLeft 0) (use 2)
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[0],target.finiteInternal.elements[1]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[3]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end LargeUse

namespace UnusedOutside
private abbrev source := outsideWeak readUsed
private abbrev target := Net.Tensor.net (weak 1) smallUsed
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[0]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[0]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[0]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[2],source.finiteEdge.elements[0],source.finiteEdge.elements[1]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end UnusedOutside


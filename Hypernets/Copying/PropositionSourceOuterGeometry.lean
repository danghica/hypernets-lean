import Hypernets.Copying.PropositionSourceInner
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Hypernets.Copying.Proposition12_2.Source
open Graph

namespace SequenceFactor
private abbrev source := sequenceNormal
private abbrev target := sequenceParts callbackTree privateTree
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[17],target.finiteInternal.elements[4],target.finiteInternal.elements[18],target.finiteInternal.elements[5],target.finiteInternal.elements[0],target.finiteInternal.elements[1],target.finiteInternal.elements[19],target.finiteInternal.elements[6],target.finiteInternal.elements[2],target.finiteInternal.elements[3],target.finiteInternal.elements[7],target.finiteInternal.elements[20],target.finiteInternal.elements[8],target.finiteInternal.elements[21],target.finiteInternal.elements[9],target.finiteInternal.elements[22],target.finiteInternal.elements[10],target.finiteInternal.elements[15],target.finiteInternal.elements[16],target.finiteInternal.elements[23],target.finiteInternal.elements[24],target.finiteInternal.elements[25],target.finiteInternal.elements[11],target.finiteInternal.elements[12],target.finiteInternal.elements[26],target.finiteInternal.elements[27],target.finiteInternal.elements[13],target.finiteInternal.elements[14]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[4],source.finiteInternal.elements[5],source.finiteInternal.elements[8],source.finiteInternal.elements[9],source.finiteInternal.elements[1],source.finiteInternal.elements[3],source.finiteInternal.elements[7],source.finiteInternal.elements[10],source.finiteInternal.elements[12],source.finiteInternal.elements[14],source.finiteInternal.elements[16],source.finiteInternal.elements[22],source.finiteInternal.elements[23],source.finiteInternal.elements[26],source.finiteInternal.elements[27],source.finiteInternal.elements[17],source.finiteInternal.elements[18],source.finiteInternal.elements[0],source.finiteInternal.elements[2],source.finiteInternal.elements[6],source.finiteInternal.elements[11],source.finiteInternal.elements[13],source.finiteInternal.elements[15],source.finiteInternal.elements[19],source.finiteInternal.elements[20],source.finiteInternal.elements[21],source.finiteInternal.elements[24],source.finiteInternal.elements[25]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[16],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[3],target.finiteEdge.elements[4],target.finiteEdge.elements[17],target.finiteEdge.elements[18],target.finiteEdge.elements[5],target.finiteEdge.elements[6],target.finiteEdge.elements[15],target.finiteEdge.elements[19],target.finiteEdge.elements[20],target.finiteEdge.elements[7],target.finiteEdge.elements[21],target.finiteEdge.elements[8],target.finiteEdge.elements[28],target.finiteEdge.elements[22],target.finiteEdge.elements[23],target.finiteEdge.elements[24],target.finiteEdge.elements[9],target.finiteEdge.elements[10],target.finiteEdge.elements[11],target.finiteEdge.elements[25],target.finiteEdge.elements[26],target.finiteEdge.elements[27],target.finiteEdge.elements[12],target.finiteEdge.elements[13],target.finiteEdge.elements[14]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[8],source.finiteEdge.elements[9],source.finiteEdge.elements[13],source.finiteEdge.elements[15],source.finiteEdge.elements[20],source.finiteEdge.elements[21],source.finiteEdge.elements[22],source.finiteEdge.elements[26],source.finiteEdge.elements[27],source.finiteEdge.elements[28],source.finiteEdge.elements[10],source.finiteEdge.elements[1],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[11],source.finiteEdge.elements[12],source.finiteEdge.elements[14],source.finiteEdge.elements[17],source.finiteEdge.elements[18],source.finiteEdge.elements[19],source.finiteEdge.elements[23],source.finiteEdge.elements[24],source.finiteEdge.elements[25],source.finiteEdge.elements[16]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8],source.finiteEdge.elements[9],source.finiteEdge.elements[10],source.finiteEdge.elements[11],source.finiteEdge.elements[12],source.finiteEdge.elements[13],source.finiteEdge.elements[14],source.finiteEdge.elements[15],source.finiteEdge.elements[16],source.finiteEdge.elements[17],source.finiteEdge.elements[18],source.finiteEdge.elements[19],source.finiteEdge.elements[20],source.finiteEdge.elements[21],source.finiteEdge.elements[22],source.finiteEdge.elements[23],source.finiteEdge.elements[24],source.finiteEdge.elements[25],source.finiteEdge.elements[26],source.finiteEdge.elements[27],source.finiteEdge.elements[28]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end SequenceFactor

namespace SequenceUse
private abbrev source := sequenceParts (use 1) (use 1)
private abbrev target := insideUse (Parametricity.callReadBody 0)
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[3],target.finiteInternal.elements[1],target.finiteInternal.elements[4],target.finiteInternal.elements[0],target.finiteInternal.elements[5],target.finiteInternal.elements[6],target.finiteInternal.elements[7]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[4],source.finiteInternal.elements[2],source.finiteInternal.elements[0],source.finiteInternal.elements[1],source.finiteInternal.elements[3],source.finiteInternal.elements[5],source.finiteInternal.elements[6],source.finiteInternal.elements[7]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[7],target.finiteEdge.elements[8],target.finiteEdge.elements[3],target.finiteEdge.elements[4],target.finiteEdge.elements[5],target.finiteEdge.elements[6]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8],source.finiteEdge.elements[3],source.finiteEdge.elements[4]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end SequenceUse

namespace AbstractionSuffix
private abbrev source := Serial.net (Serial.net (Parametricity.largeLeft 0) (use 2)) (Translation.singleUse 2 1 0)
private abbrev target := bodyNormal
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[2],target.finiteInternal.elements[0],target.finiteInternal.elements[1],target.finiteInternal.elements[3],target.finiteInternal.elements[4]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[0],source.finiteInternal.elements[3],source.finiteInternal.elements[4]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[3],target.finiteEdge.elements[4],target.finiteEdge.elements[5]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end AbstractionSuffix

namespace Opened
private abbrev source := opened
private abbrev target := Serial.net (raise 2 body) (Parametricity.privateCell 3)
private instance : DecidableEq source.Internal := by graph_decide_eq
private instance : DecidableEq target.Internal := by graph_decide_eq
private instance : DecidableEq source.Edge := by graph_decide_eq
private instance : DecidableEq target.Edge := by graph_decide_eq
private def vertices : Bijection source.Internal target.Internal :=
  FiniteGraphCertificate.bijection source.finiteInternal target.finiteInternal
    (FiniteGraphCertificate.table source.finiteInternal.elements [target.finiteInternal.elements[6],target.finiteInternal.elements[0],target.finiteInternal.elements[1],target.finiteInternal.elements[2],target.finiteInternal.elements[3],target.finiteInternal.elements[4],target.finiteInternal.elements[5],target.finiteInternal.elements[7]] target.finiteInternal.elements[0])
    (FiniteGraphCertificate.table target.finiteInternal.elements [source.finiteInternal.elements[1],source.finiteInternal.elements[2],source.finiteInternal.elements[3],source.finiteInternal.elements[4],source.finiteInternal.elements[5],source.finiteInternal.elements[6],source.finiteInternal.elements[0],source.finiteInternal.elements[7]] source.finiteInternal.elements[0])
    (by decide) (by decide)
private def edges : Bijection source.Edge target.Edge :=
  FiniteGraphCertificate.bijection source.finiteEdge target.finiteEdge
    (FiniteGraphCertificate.table source.finiteEdge.elements [target.finiteEdge.elements[0],target.finiteEdge.elements[1],target.finiteEdge.elements[2],target.finiteEdge.elements[3],target.finiteEdge.elements[4],target.finiteEdge.elements[5],target.finiteEdge.elements[6],target.finiteEdge.elements[7],target.finiteEdge.elements[8]] target.finiteEdge.elements[0])
    (FiniteGraphCertificate.table target.finiteEdge.elements [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8]] source.finiteEdge.elements[0])
    (by decide) (by decide)

/-- Explicit bijections check every ordered incidence and retain the whole box body. -/
def iso : DeepIso source target :=
  FiniteGraphCertificate.iso source target vertices edges
    (by
      intro e member
      change e ∈ [source.finiteEdge.elements[0],source.finiteEdge.elements[1],source.finiteEdge.elements[2],source.finiteEdge.elements[3],source.finiteEdge.elements[4],source.finiteEdge.elements[5],source.finiteEdge.elements[6],source.finiteEdge.elements[7],source.finiteEdge.elements[8]] at member
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact labelEquiv_refl _ _)
    (by decide) (by decide) (by decide)
end Opened


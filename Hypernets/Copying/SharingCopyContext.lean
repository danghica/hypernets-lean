import Hypernets.Copying.MaximalSharingComponent
import Hypernets.Copying.SharingPayloadBoundary
import Hypernets.Copying.SerialExpansion
import Hypernets.Copying.SerialComponents
import Hypernets.Copying.CommonContextLocalIso
import Hypernets.Copying.RetainedFootprintNormalisation

/-! A maximal term-sharing basin and the actual copyable payload assemble to
a complete original common-context source, including every selected old hole. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingCopyContext
open Graph Opening RetainedFootprint
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) (f : Occurrence G (C.expand L))
    (S : C.RootedBasin Wire.term)
    (labels : ∀ e, S.chosen e → SharingBasin.Eligible C .term e)
    (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)

noncomputable abbrev payload := skeleton C f cert (SharingPayload.avoids C cert trees copyable f)
noncomputable abbrev payloadOccurrence := skeletonOccurrence C f cert (SharingPayload.avoids C cert trees copyable f)
noncomputable abbrev tree : SharingTreeContext .term inputs.length d := SharingBasin.context (G := C) (s := .term) S labels inputs distinct boundary
noncomputable abbrev treeOccurrence : Occurrence
    (tree C S labels inputs distinct boundary).net C := SharingBasin.occurrence (G := C) (s := .term) S labels inputs distinct boundary
noncomputable abbrev source := Serial.net (tree C S labels inputs distinct boundary).net (payload C cert trees copyable f)

include cert trees copyable in
/-- Disjointness of this maximal component and payload follows from their
original owner labels, including all original sharing-template holes. -/
theorem disjoint : ∀ e a,
    (treeOccurrence C S labels inputs distinct boundary).edges e ≠
      (payloadOccurrence C cert trees copyable f).edges a := by
  intro e a eq
  have sharing := labels e.val e.property
  change SharingLabel d .term (C.edgeLabel e.val) at sharing
  have same : e.val = (f.edges a).1 := eq
  rw [same] at sharing
  exact SharingPayload.owner_notSharing C cert trees copyable f .term a sharing

variable (join : S.output = port C f.matchEmbedding cert
    (SharingPayload.avoids C cert trees copyable f) (.input 0))

include join in
theorem serialBoundary (i : Fin [Wire.term].length) :
    (treeOccurrence C S labels inputs distinct boundary).ports (.output i) =
      (payloadOccurrence C cert trees copyable f).ports (.input i) := by
  have zero : i = 0 := Fin.ext (by have h : i.val < 1 := i.isLt; change i.val = 0; omega)
  subst i
  exact join

/-- This actual occurrence includes both the entire original sharing basin
and the retained payload skeleton, with the original ordered junction. -/
noncomputable def occurrence : Occurrence
    (source C cert trees copyable f S labels inputs distinct boundary) C :=
  Occurrence.SerialJoin.occurrence
    (treeOccurrence C S labels inputs distinct boundary)
    (payloadOccurrence C cert trees copyable f)
    (serialBoundary C cert trees copyable f S labels inputs distinct boundary join)
    (disjoint C cert trees copyable f S labels inputs distinct boundary)

include join in
theorem occurrence_input (i : Fin (List.replicate inputs.length Wire.term).length) :
    (occurrence C cert trees copyable f S labels inputs distinct boundary join).ports (.input i) =
      (inputs.get ⟨i.val,by simpa using i.isLt⟩).val :=
  Occurrence.SerialJoin.occurrence_input _ _ _ _ i

omit join in
/-- Select exactly the original fillings belonging to the joined source. -/
noncomputable def family
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) :
    (e : (source C cert trees copyable f S labels inputs distinct boundary).Edge) →
      Hypernet d ((alphabet d).signature.input
        ((source C cert trees copyable f S labels inputs distinct boundary).edgeLabel e))
        ((alphabet d).signature.output
        ((source C cert trees copyable f S labels inputs distinct boundary).edgeLabel e)) := by
  clear join
  cases d
  all_goals
    rintro ⟨b,e⟩
    cases b
    · exact F e.val
    · exact F (f.edges e).1

/-- Normalizing this complete original cut does not change its expanded
graph: its source already uses the original labels on every edge. -/
noncomputable def localSourceIso
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) :
    DeepIso
      ((CommonContextCut.skeleton C
        (occurrence C cert trees copyable f S labels inputs distinct boundary join)).expand
        (CommonContextCut.localFamily C
          (occurrence C cert trees copyable f S labels inputs distinct boundary join) F))
      ((source C cert trees copyable f S labels inputs distinct boundary).expand
        (family C cert trees copyable f S labels inputs distinct boundary F)) := by
  apply CommonContextCut.localIso C
    (occurrence C cert trees copyable f S labels inputs distinct boundary join) F
    (family C cert trees copyable f S labels inputs distinct boundary F)
  intro e
  cases d
  all_goals
    obtain ⟨b,e⟩ := e
    cases b
    · change DeepIso ((F e.val).reboundary _ _) (F e.val)
      simpa only [Net.reboundary_refl] using DeepIso.refl (F e.val)
    · change DeepIso ((F (f.edges e).1).reboundary _ _) (F (f.edges e).1)
      simpa only [Net.reboundary_refl] using DeepIso.refl (F (f.edges e).1)

/-- Expansion through the complete selected source separates into its original
sharing and payload expansions, with no distributivity equation assumed. -/
noncomputable def splitIso :
    DeepIso
      ((source C cert trees copyable f S labels inputs distinct boundary).expand
        (family C cert trees copyable f S labels inputs distinct boundary L))
      (Serial.net
        ((tree C S labels inputs distinct boundary).net.expand
          (SharingBasin.selectedLeft (s := .term) C (L := L) S))
        ((payload C cert trees copyable f).expand
          (leftFamily C f cert (SharingPayload.avoids C cert trees copyable f)))) := by
  clear join
  have split := Serial.expansionIso
    (tree C S labels inputs distinct boundary).net (payload C cert trees copyable f)
    (family C cert trees copyable f S labels inputs distinct boundary L)
  apply split.trans
  apply Serial.congr
  · apply Net.ExpansionIso.iso
    intro e
    cases d <;> exact DeepIso.refl _
  · apply Net.ExpansionIso.iso
    intro e
    cases d <;> exact DeepIso.refl _

/-- The left local source is the literal original copy-rule source with the
whole maximal tree; the payload is reconstructed from the actual occurrence. -/
noncomputable def leftIso (closed : HoleFree (C.expand L)) :
    DeepIso
      ((CommonContextCut.skeleton C
        (occurrence C cert trees copyable f S labels inputs distinct boundary join)).expand
        (CommonContextCut.localFamily C
          (occurrence C cert trees copyable f S labels inputs distinct boundary join) L))
      (Serial.net
        ((SharingBasin.leftTree (s := .term) C cert trees S labels inputs distinct boundary closed).atDepth d) G) :=
  (localSourceIso C cert trees copyable f S labels inputs distinct boundary join L).trans
    ((splitIso C cert trees copyable f S labels inputs distinct boundary).trans
      (Serial.congr
        (((tree C S labels inputs distinct boundary).left_sharingTreeGraph
          (SharingBasin.selectedCertificates (s := .term) C cert S labels inputs distinct boundary) trees
          (SharingBasin.selectedClosed (s := .term) C S labels inputs distinct boundary closed)).treeIso.symm)
        (reconstruction C f cert (SharingPayload.avoids C cert trees copyable f))))

/-- Expansion through the complete selected source separates into its original
sharing and payload expansions, with no distributivity equation assumed. -/
noncomputable def rightSplitIso :
    DeepIso
      ((source C cert trees copyable f S labels inputs distinct boundary).expand
        (family C cert trees copyable f S labels inputs distinct boundary R))
      (Serial.net
        ((tree C S labels inputs distinct boundary).net.expand
          (SharingBasin.selectedRight (s := .term) C (R := R) S))
        ((payload C cert trees copyable f).expand
          (rightFamily C f cert (SharingPayload.avoids C cert trees copyable f)))) := by
  clear join
  have split := Serial.expansionIso
    (tree C S labels inputs distinct boundary).net (payload C cert trees copyable f)
    (family C cert trees copyable f S labels inputs distinct boundary R)
  apply split.trans
  apply Serial.congr
  · apply Net.ExpansionIso.iso
    intro e
    cases d <;> exact DeepIso.refl _
  · apply Net.ExpansionIso.iso
    intro e
    cases d <;> exact DeepIso.refl _

/-- The right local source retains the original paired payload expansion and
the independently normalized maximal right tree. -/
noncomputable def rightIso (closed : HoleFree (C.expand L)) :
    DeepIso
      ((CommonContextCut.skeleton C
        (occurrence C cert trees copyable f S labels inputs distinct boundary join)).expand
        (CommonContextCut.localFamily C
          (occurrence C cert trees copyable f S labels inputs distinct boundary join) R))
      (Serial.net
        ((SharingBasin.rightTree (s := .term) C cert trees S labels inputs distinct boundary closed).atDepth d)
        ((payload C cert trees copyable f).expand
          (rightFamily C f cert (SharingPayload.avoids C cert trees copyable f)))) :=
  (localSourceIso C cert trees copyable f S labels inputs distinct boundary join R).trans
    ((rightSplitIso C cert trees copyable f S labels inputs distinct boundary).trans
      (Serial.congr
        (((tree C S labels inputs distinct boundary).right_sharingTreeGraph
          (SharingBasin.selectedCertificates (s := .term) C cert S labels inputs distinct boundary) trees
          (SharingBasin.selectedClosed (s := .term) C S labels inputs distinct boundary closed)).treeIso.symm)
        (DeepIso.refl _)))

end Hypernets.Copying.SharingCopyContext

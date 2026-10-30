import Hypernets.Copying.SharingBasinFillings
import Hypernets.Copying.CommonContextLocalIso

/-! Exact source normalization of maximal original sharing contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingBasin
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    {s : ShareSort} (S : C.RootedBasin s.wire)
    (labels : ∀ e, S.chosen e → Eligible C s e)
    (inputs : List S.Vertex) (distinct : inputs.Nodup)
    (boundary : ∀ v, v ∈ inputs ↔ S.Input v)

/-- The selected context already has the literal original host labels. -/
noncomputable def localExpansionIso
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) :
    DeepIso
      ((CommonContextCut.skeleton C (occurrence S labels inputs distinct boundary)).expand
        (CommonContextCut.localFamily C (occurrence S labels inputs distinct boundary) F))
      ((context S labels inputs distinct boundary).net.expand (fun e => F e.val)) := by
  apply CommonContextCut.localIso C (occurrence S labels inputs distinct boundary) F
    (fun e => F e.val)
  intro e
  change DeepIso ((F e.val).reboundary _ _) (F e.val)
  simpa only [Net.reboundary_refl] using DeepIso.refl (F e.val)

/-- The normalized selected left cut is its complete primitive sharing tree. -/
noncomputable def localLeftIso (closed : HoleFree (C.expand L)) :
    DeepIso
      ((CommonContextCut.skeleton C (occurrence S labels inputs distinct boundary)).expand
        (CommonContextCut.localFamily C (occurrence S labels inputs distinct boundary) L))
      ((leftTree C cert trees S labels inputs distinct boundary closed).atDepth d) :=
  (localExpansionIso C S labels inputs distinct boundary L).trans
    (((selectedContext C S labels inputs distinct boundary).left_sharingTreeGraph
      (selectedCertificates C cert S labels inputs distinct boundary) trees
      (selectedClosed C S labels inputs distinct boundary closed)).treeIso.symm)

/-- The right cut is independently the corresponding complete sharing tree. -/
noncomputable def localRightIso (closed : HoleFree (C.expand L)) :
    DeepIso
      ((CommonContextCut.skeleton C (occurrence S labels inputs distinct boundary)).expand
        (CommonContextCut.localFamily C (occurrence S labels inputs distinct boundary) R))
      ((rightTree C cert trees S labels inputs distinct boundary closed).atDepth d) :=
  (localExpansionIso C S labels inputs distinct boundary R).trans
    (((selectedContext C S labels inputs distinct boundary).right_sharingTreeGraph
      (selectedCertificates C cert S labels inputs distinct boundary) trees
      (selectedClosed C S labels inputs distinct boundary closed)).treeIso.symm)

end Hypernets.Copying.SharingBasin

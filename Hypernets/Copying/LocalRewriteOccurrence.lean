import Hypernets.Copying.PrimitiveRuleFootprints
import Hypernets.Copying.MatchEmbeddingGeometry

/-! Recover a full-label occurrence from the original contextual rewrite
derivation. Recursive box labels are retained, not weakened to primitive-only
matching, so finite context reconstruction has its actual required premises. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- A complete-label match already determines a typed, injective occurrence of
its internal vertices. These properties follow from incidence laws. -/
noncomputable def MatchEmbedding.occurrence {d I O J K}
    {A : Hypernet d J K} {G : Hypernet d I O} (f : MatchEmbedding A G)
    (labels : ∀ e, LabelEquiv d (A.edgeLabel e) (G.edgeLabel (f.edges e))) :
    Opening.Occurrence A G where
  ports := f.ports
  internals := f.internal
  edges := f.edges
  internal_map := f.ports_internal
  internal_injective := f.internal_injective
  edge_injective := f.edge_injective
  internal_label a := by
    have eq := f.vertexLabel labels (.internal a)
    rw [f.ports_internal] at eq
    exact eq
  label := labels
  source := f.source
  target := f.target

namespace Combined

/-- Every original local/rename/plug/expand derivation contains an actual local
rule with a full recursive-label occurrence at its actual initial token. -/
theorem Rewrite.local_occurrence {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) :
    ∃ J K, ∃ A B : Hypernet d J K, ∃ a b, Local A a B b ∧
      ∃ f : Opening.Occurrence A G, f.ports a = v := by
  induction step with
  | @«local» I O G v H w h => exact ⟨_,_,_,_,_,_,h,Opening.Occurrence.ofIso (DeepIso.refl _),by cases v <;> rfl⟩
  | rename f g step ih =>
    obtain ⟨J,K,A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K,A,B,a,b,h,q.comp (Opening.Occurrence.ofIso f),
      congrArg (Port.map f.vertices.toFun) eq⟩
  | plug C e step ih =>
    obtain ⟨J,K,A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K,A,B,a,b,h,q.comp (Opening.Occurrence.plug C e _),
      congrArg (Net.Replacement.insert C e _) eq⟩
  | expand C F K e others step ih =>
    obtain ⟨J,K',A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K',A,B,a,b,h,q.comp (Opening.Occurrence.expand C F e),
      congrArg (Net.Expansion.insert C F e) eq⟩

end Combined
end Hypernets.Copying

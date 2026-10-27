import Hypernets.Copying.BPermOverlapClassification

/-! Actual rewrite heads and copying paths originate in the original context;
the application frame reaches exactly the box slot classified above. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation
open Graph Combined MatchEmbedding
variable {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
include cert

/-- An incidence leaving a primitive edge reflects even when the next edge is
a shallow box contribution whose external output order has been permuted. -/
theorem adjacent_origin {a b : (C.expand L).Edge} {p}
    (label : (C.expand L).edgeLabel a = primitiveLabel d p)
    (adjacent : (C.expand L).Adjacent a b) : C.Adjacent a.1 b.1 := by
  obtain ⟨v,ht,hs⟩ := adjacent
  refine ⟨PrimitiveMatching.down C cert v,?_,?_⟩
  · rw [← PrimitiveMatching.target_down C cert a label]
    exact List.mem_map_of_mem ht
  · apply Search.Expansion.source_owner C L (e := b.1) (x := b.2)
    rw [PrimitiveMatching.host_down]
    exact hs

theorem head_origin {v e p} (head : HeadAt (C.expand L) v e p) :
    HeadAt C (PrimitiveMatching.down C cert v) e.1 p := by
  refine ⟨(primitive_origin cert e p head.1).1,?_⟩
  rw [← PrimitiveMatching.source_down C cert e head.1]
  exact List.mem_map_of_mem head.2

/-- Copying's term-sharing hops cannot be supplied by a shallow BPerm hole. -/
theorem copy_hop_origin {a b : (C.expand L).Edge} (hop : CopyTrace.Hop (C.expand L) a b) :
    CopyTrace.Hop C a.1 b.1 := by
  rcases hop.1 with contraction | weakening
  · exact ⟨.inl (primitive_origin cert a _ contraction).1,adjacent_origin C cert contraction hop.2⟩
  · exact ⟨.inr (primitive_origin cert a _ weakening).1,adjacent_origin C cert weakening hop.2⟩

/-- Reflect the whole counted tree path, not just its endpoints. -/
theorem copy_path_origin {a b : (C.expand L).Edge} {n}
    (path : Trace (CopyTrace.Hop (C.expand L)) a b n) :
    Trace (CopyTrace.Hop C) a.1 b.1 n :=
  path.map Sigma.fst (copy_hop_origin C cert)

theorem copy_resolution_origin {v e p n}
    (resolved : CopyTrace.Resolves (C.expand L) v e p n) :
    CopyTrace.Resolves C (PrimitiveMatching.down C cert v) e.1 p n := by
  obtain ⟨a,src,path,label,kind⟩ := resolved
  refine ⟨a.1,?_,copy_path_origin C cert path,(primitive_origin cert e p label).1,kind⟩
  apply Search.Expansion.source_owner C L (e := a.1) (x := a.2)
  rw [PrimitiveMatching.host_down]
  exact src

/-- Every actual full-machine rewrite is rooted at a retained original primitive
head. This includes the other operation families, not just beta and copying. -/
theorem rewrite_head_origin {H : Hypernet d I O} {v w}
    (step : Rewrite (C.expand L) v H w) :
    ∃ choice e, Recognizes (C.expand L) v choice ∧
      HeadAt C (PrimitiveMatching.down C cert v) e choice.head ∧
      ∀ h, C.edgeLabel e ≠ primitiveLabel d (.hole h) := by
  obtain ⟨choice,recognized⟩ := rewrite_recognizes step
  obtain ⟨e,head,data⟩ := recognized
  have old := head_origin C cert head
  refine ⟨choice,e.1,⟨e,head,data⟩,old,?_⟩
  intro h hole
  have eq := primitiveLabel_injective d (old.1.symm.trans hole)
  cases choice <;> cases eq

end Hypernets.Copying.BoxPermutation

namespace Hypernets.Copying.BoxPermutation.ApplicationOverlap
open Graph
variable {d I O} {C : Hypernet (d+1) I O} {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    {k h v} {B : Hypernet d [.term] (environmentInterface (k+1) h)}
    (a : Application.Match (C.expand L) v B)
include cert

/-- The actual two-edge application/lambda prefix reaches the original box or
hole classified by BoxOrigin. There are no extra inserted outer vertices. -/
theorem frame_path :
    C.Adjacent a.app.1 a.lam.1 ∧ C.Adjacent a.lam.1 a.boxEdge.1 := by
  constructor
  · apply adjacent_origin C cert a.head_at.1
    refine ⟨.internal a.functionWire,?_,?_⟩
    · rw [a.app_target]; exact List.mem_cons_self
    · rw [a.lambda_source]; exact List.mem_cons_self
  · apply adjacent_origin C cert a.lambda_label
    refine ⟨.internal a.thunkWire,?_,?_⟩
    · rw [a.lambda_target]; exact List.mem_cons_self
    · rw [a.box_source]; exact List.mem_cons_self

theorem counted_frame_path : Trace C.Adjacent a.app.1 a.boxEdge.1 2 :=
  .step (frame_path cert a).1 (.step (frame_path cert a).2 (.refl _))
end Hypernets.Copying.BoxPermutation.ApplicationOverlap

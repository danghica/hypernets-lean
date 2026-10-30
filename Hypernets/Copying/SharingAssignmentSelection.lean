import Hypernets.Copying.SharingBinaryOrigin
import Hypernets.Copying.SharingAssignmentContext

/-! An arbitrary original assignment occurrence determines its whole maximal
atom context and the unchanged stable value in the original common context. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph Opening

def treeOccurrence {d h K} (A : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) :
    Occurrence (A.atDepth d) (before A G) := by
  cases d <;> exact Occurrence.expand (beforePattern _ h K) (beforeFill A G) .tree

def valueOccurrence {d h K} (A : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) :
    Occurrence G (before A G) := by
  cases d <;> exact Occurrence.expand (beforePattern _ h K) (beforeFill A G) .value

def beforeAssign {d h K} (A : ContractionTree .atom (h+1)) (G : Hypernet d [.term] K) :
    (before A G).Edge := by cases d <;> exact ⟨.assign,(0 : Fin 1)⟩

end Hypernets.Copying.Assignment
namespace Hypernets.Copying.MaximalSharing
open Graph Opening
variable {T : PreTemplate} {d I O K} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
    (closed : HoleFree (C.expand L))
    {n} (A : ContractionTree .atom (n+1)) (G : Hypernet d [.term] K) (stable : Stable G)
    (f : Occurrence (Assignment.before A G) (C.expand L))

noncomputable def assignment_value : Occurrence G C :=
  SharingOverlap.primitiveOccurrence C cert trees closed ((Assignment.valueOccurrence A G).comp f)
    (SharingOverlap.stable_nonsharing stable) (BoxPermutation.PrimitiveFootprint.stable stable)

include cert trees closed stable
/-- The actual instance and store determine the full atom basin, while the
ordered assignment arguments determine its entry and original stable value. -/
theorem assignment_selection {token : C.Vertex}
    (attached : f.ports (Assignment.inputPort n K 0) = Net.Expansion.host C L token) :
    ∃ S : C.RootedBasin Wire.atom, ∃ _labels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex, ∃ u w o : C.Vertex,
        (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        C.edgeLabel (f.edges (Assignment.beforeAssign A G)).1 = primitiveLabel d (.operation (.binary .assign)) ∧
        C.edgeLabel (f.edges (Assignment.beforeInstance A G)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (Assignment.beforeStore A G)).1 = primitiveLabel d .store ∧
        C.source (f.edges (Assignment.beforeAssign A G)).1 = [token] ∧
        C.target (f.edges (Assignment.beforeAssign A G)).1 = [u,w] ∧
        C.source (f.edges (Assignment.beforeInstance A G)).1 = [u] ∧
        C.target (f.edges (Assignment.beforeInstance A G)).1 = [a.val] ∧
        C.source (f.edges (Assignment.beforeStore A G)).1 = [S.output] ∧
        C.target (f.edges (Assignment.beforeStore A G)).1 = [o] ∧
        (assignment_value C cert trees closed A G stable f).ports (.input 0) = w := by
  let tree := (Assignment.treeOccurrence A G).comp f
  have al := f.matchEmbedding.primitive (Assignment.beforeAssign A G) (.operation (.binary .assign)) (by cases d <;> rfl)
  have il := f.matchEmbedding.primitive (Assignment.beforeInstance A G) .instanceEdge (by cases d <;> rfl)
  have sl := f.matchEmbedding.primitive (Assignment.beforeStore A G) .store (by cases d <;> rfl)
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeAssign A G)) = _ at al
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeInstance A G)) = _ at il
  change (C.expand L).edgeLabel (f.edges (Assignment.beforeStore A G)) = _ at sl
  let first : (Assignment.before A G).Vertex := by cases d <;> exact .internal (.inl (0 : Fin 4))
  let second : (Assignment.before A G).Vertex := by cases d <;> exact .internal (.inl (1 : Fin 4))
  have asrc : (C.expand L).source (f.edges (Assignment.beforeAssign A G)) = [f.ports (Assignment.inputPort n K 0)] := by
    rw [← f.source]; cases d <;> rfl
  have atgt : (C.expand L).target (f.edges (Assignment.beforeAssign A G)) = [f.ports first,f.ports second] := by
    rw [← f.target]; cases d <;> rfl
  have isrc : (C.expand L).source (f.edges (Assignment.beforeInstance A G)) = [f.ports first] := by
    rw [← f.source]; cases d <;> rfl
  have itgt : (C.expand L).target (f.edges (Assignment.beforeInstance A G)) = [tree.ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; cases d <;> rfl
  have ssrc : (C.expand L).source (f.edges (Assignment.beforeStore A G)) = [tree.ports (.output 0)] := by
    rw [← f.source]; cases d <;> rfl
  have stgt : (C.expand L).target (f.edges (Assignment.beforeStore A G)) = [f.ports (.output ⟨0,by simp [Assignment.outputs]⟩)] := by
    rw [← f.target]; cases d <;> rfl
  obtain ⟨t,u,w,alabel,asrc',atgt',ht,hu,hw⟩ := binary_primitive_origin C cert trees al
    (by intro s; constructor <;> intro h <;> cases h) asrc atgt
  obtain ⟨u',v,ilabel,isrc',itgt',hu',hv⟩ := unary_primitive_origin C cert trees il
    (by intro s; constructor <;> intro h <;> cases h) isrc itgt
  obtain ⟨z,o,slabel,ssrc',stgt',hz,ho⟩ := unary_primitive_origin C cert trees sl
    (by intro s; constructor <;> intro h <;> cases h) ssrc stgt
  have teq : t = token := Net.Expansion.host_injective C L (ht.trans attached)
  have ueq : u' = u := Net.Expansion.host_injective C L (hu'.trans hu.symm)
  subst t; subst u'
  obtain ⟨S,labels,a,rest,entry,nd,boundary,out⟩ := atom_component C cert trees A tree sl
    (by rw [ssrc]; exact List.mem_cons_self) ⟨0,by simp⟩ il
    (by rw [itgt]; exact List.mem_cons_self)
  have aeq : a.val = v := Net.Expansion.host_injective C L (entry.trans hv.symm)
  have zeq : S.output = z := Net.Expansion.host_injective C L (out.trans hz.symm)
  refine ⟨S,labels,a,rest,u,w,o,nd,boundary,alabel,ilabel,slabel,asrc',atgt',isrc',
    aeq ▸ itgt',zeq ▸ ssrc',stgt',?_⟩
  apply Net.Expansion.host_injective C L
  rw [assignment_value,SharingOverlap.primitiveOccurrence_host]
  exact (show ((Assignment.valueOccurrence A G).comp f).ports (.input 0) = f.ports second from by cases d <;> rfl).trans hw.symm

end Hypernets.Copying.MaximalSharing

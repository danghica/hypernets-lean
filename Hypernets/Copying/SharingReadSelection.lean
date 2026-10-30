import Hypernets.Copying.MaximalAtomComponent
import Hypernets.Copying.SharingReadContext
import Hypernets.Copying.DereferenceReplacement

/-! Every original read occurrence determines its actual maximal common
sharing context and complete original reader/instance/store attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Dereference
open Graph Opening

/-- The full atom tree of the original read rule occurs with every branch. -/
def treeOccurrence {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    Occurrence (T.atDepth d) (before T d) where
  ports := beforeTreeVertex T d
  internals x := .inr ⟨.tree,x⟩
  edges := beforeTree T d
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

end Hypernets.Copying.Dereference

namespace Hypernets.Copying.MaximalSharing
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- Selected maximum-tree interfaces and original unary node coordinates
come from an arbitrary actual read occurrence, with no assumed cut match. -/
theorem read_selection {k} (A : ContractionTree .atom (k+1))
    (f : Occurrence (Dereference.before A d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (Dereference.inputPort k 0) = Net.Expansion.host C L token) :
    ∃ S : C.RootedBasin Wire.atom, ∃ _labels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a : S.Vertex, ∃ rest : List S.Vertex, ∃ u o : C.Vertex,
        (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        C.edgeLabel (f.edges ⟨.reader,(0 : Fin 1)⟩).1 = primitiveLabel d (.operation (.unary .deref)) ∧
        C.edgeLabel (f.edges (Dereference.beforeInstance A d)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (Dereference.beforeStore A d)).1 = primitiveLabel d .store ∧
        C.source (f.edges ⟨.reader,(0 : Fin 1)⟩).1 = [token] ∧
        C.target (f.edges ⟨.reader,(0 : Fin 1)⟩).1 = [u] ∧
        C.source (f.edges (Dereference.beforeInstance A d)).1 = [u] ∧
        C.target (f.edges (Dereference.beforeInstance A d)).1 = [a.val] ∧
        C.source (f.edges (Dereference.beforeStore A d)).1 = [S.output] ∧
        C.target (f.edges (Dereference.beforeStore A d)).1 = [o] := by
  let tree := (Dereference.treeOccurrence A d).comp f
  have readerLabel := f.matchEmbedding.primitive ⟨.reader,(0 : Fin 1)⟩ (.operation (.unary .deref)) rfl
  have instanceLabel := f.matchEmbedding.primitive (Dereference.beforeInstance A d) .instanceEdge rfl
  have storeLabel := f.matchEmbedding.primitive (Dereference.beforeStore A d) .store rfl
  change (C.expand L).edgeLabel (f.edges ⟨.reader,(0 : Fin 1)⟩) = _ at readerLabel
  change (C.expand L).edgeLabel (f.edges (Dereference.beforeInstance A d)) = _ at instanceLabel
  change (C.expand L).edgeLabel (f.edges (Dereference.beforeStore A d)) = _ at storeLabel
  have readerSource : (C.expand L).source (f.edges ⟨.reader,(0 : Fin 1)⟩) = [f.ports (Dereference.inputPort k 0)] := by
    rw [← f.source]; rfl
  have readerTarget : (C.expand L).target (f.edges ⟨.reader,(0 : Fin 1)⟩) = [f.ports (.internal (.inl (0 : Fin 3)))] := by
    rw [← f.target]; rfl
  have instanceSource : (C.expand L).source (f.edges (Dereference.beforeInstance A d)) = [f.ports (.internal (.inl (0 : Fin 3)))] := by
    rw [← f.source]; rfl
  have instanceTarget : (C.expand L).target (f.edges (Dereference.beforeInstance A d)) = [tree.ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; rfl
  have storeSource : (C.expand L).source (f.edges (Dereference.beforeStore A d)) = [tree.ports (.output 0)] := by
    rw [← f.source]; rfl
  have storeTarget : (C.expand L).target (f.edges (Dereference.beforeStore A d)) = [f.ports (.output 0)] := by
    rw [← f.target]; rfl
  obtain ⟨t,u,rlabel,rsrc,rtgt,ht,hu⟩ := unary_primitive_origin C cert trees readerLabel
    (by intro s; constructor <;> intro h <;> cases h) readerSource readerTarget
  obtain ⟨u',v,ilabel,isrc,itgt,hu',hv⟩ := unary_primitive_origin C cert trees instanceLabel
    (by intro s; constructor <;> intro h <;> cases h) instanceSource instanceTarget
  obtain ⟨z,o,slabel,ssrc,stgt,hz,ho⟩ := unary_primitive_origin C cert trees storeLabel
    (by intro s; constructor <;> intro h <;> cases h) storeSource storeTarget
  have tEq : t = token := Net.Expansion.host_injective C L (ht.trans attached)
  have uEq : u' = u := Net.Expansion.host_injective C L (hu'.trans hu.symm)
  subst t; subst u'
  obtain ⟨S,labels,a,rest,entry,nd,boundary,out⟩ := atom_component C cert trees A tree storeLabel
    (by rw [storeSource]; exact List.mem_cons_self) ⟨0,by simp⟩ instanceLabel
    (by rw [instanceTarget]; exact List.mem_cons_self)
  have aEq : a.val = v := Net.Expansion.host_injective C L (entry.trans hv.symm)
  have outEq : S.output = z := Net.Expansion.host_injective C L (out.trans hz.symm)
  exact ⟨S,labels,a,rest,u,o,nd,boundary,rlabel,ilabel,slabel,rsrc,rtgt,isrc,
    aEq ▸ itgt,outEq ▸ ssrc,stgt⟩

end Hypernets.Copying.MaximalSharing

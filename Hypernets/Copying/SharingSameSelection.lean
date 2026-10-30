import Hypernets.Copying.SharingBinaryOrigin
import Hypernets.Copying.SharingSameContext
import Hypernets.Copying.AtomEqualityResolution

/-! The two selected instances of a true comparison select two distinct
ordered entries of one complete original atom-sharing component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Same
open Graph Opening

def treeOccurrence {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Occurrence (T.atDepth d) (before T d) where
  ports := beforeLeftVertex T d
  internals x := .inr ⟨.tree,x⟩
  edges x := ⟨.tree,x⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl
end Hypernets.Copying.AtomEquality.Same

namespace Hypernets.Copying.MaximalSharing
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

theorem same_selection {k} (A : ContractionTree .atom (k+2))
    (f : Occurrence (AtomEquality.Same.before A d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Same.inputPort k 0) = Net.Expansion.host C L token) :
    ∃ S : C.RootedBasin Wire.atom, ∃ _labels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a b : S.Vertex, ∃ rest : List S.Vertex, ∃ u u' o : C.Vertex,
        (a::b::rest).Nodup ∧ (∀ x, x ∈ a::b::rest ↔ S.Input x) ∧
        C.edgeLabel (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = primitiveLabel d (.operation (.binary .atomEq)) ∧
        C.edgeLabel (f.edges (AtomEquality.Same.beforeLeft A d)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (AtomEquality.Same.beforeRight A d)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (AtomEquality.Same.beforeStore A d)).1 = primitiveLabel d .store ∧
        C.source (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = [token] ∧
        C.target (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = [u,u'] ∧
        C.source (f.edges (AtomEquality.Same.beforeLeft A d)).1 = [u] ∧
        C.target (f.edges (AtomEquality.Same.beforeLeft A d)).1 = [a.val] ∧
        C.source (f.edges (AtomEquality.Same.beforeRight A d)).1 = [u'] ∧
        C.target (f.edges (AtomEquality.Same.beforeRight A d)).1 = [b.val] ∧
        C.source (f.edges (AtomEquality.Same.beforeStore A d)).1 = [S.output] ∧
        C.target (f.edges (AtomEquality.Same.beforeStore A d)).1 = [o] := by
  let tree := (AtomEquality.Same.treeOccurrence A d).comp f
  have compareLabel := f.matchEmbedding.primitive ⟨.compare,(0 : Fin 1)⟩ (.operation (.binary .atomEq)) rfl
  have firstLabel := f.matchEmbedding.primitive (AtomEquality.Same.beforeLeft A d) .instanceEdge rfl
  have secondLabel := f.matchEmbedding.primitive (AtomEquality.Same.beforeRight A d) .instanceEdge rfl
  have storeLabel := f.matchEmbedding.primitive (AtomEquality.Same.beforeStore A d) .store rfl
  change (C.expand L).edgeLabel (f.edges ⟨.compare,(0 : Fin 1)⟩) = _ at compareLabel
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Same.beforeLeft A d)) = _ at firstLabel
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Same.beforeRight A d)) = _ at secondLabel
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Same.beforeStore A d)) = _ at storeLabel
  have compareSource : (C.expand L).source (f.edges ⟨.compare,(0 : Fin 1)⟩) = [f.ports (AtomEquality.Same.inputPort k 0)] := by
    rw [← f.source]; rfl
  have compareTarget : (C.expand L).target (f.edges ⟨.compare,(0 : Fin 1)⟩) =
      [f.ports (.internal (.inl (0 : Fin 5))),f.ports (.internal (.inl (1 : Fin 5)))] := by
    rw [← f.target]; rfl
  have firstSource : (C.expand L).source (f.edges (AtomEquality.Same.beforeLeft A d)) = [f.ports (.internal (.inl (0 : Fin 5)))] := by
    rw [← f.source]; rfl
  have firstTarget : (C.expand L).target (f.edges (AtomEquality.Same.beforeLeft A d)) = [tree.ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; rfl
  have secondSource : (C.expand L).source (f.edges (AtomEquality.Same.beforeRight A d)) = [f.ports (.internal (.inl (1 : Fin 5)))] := by
    rw [← f.source]; rfl
  have secondTarget : (C.expand L).target (f.edges (AtomEquality.Same.beforeRight A d)) = [tree.ports (.input ⟨1,by simp⟩)] := by
    rw [← f.target]; rfl
  have storeSource : (C.expand L).source (f.edges (AtomEquality.Same.beforeStore A d)) = [tree.ports (.output 0)] := by
    rw [← f.source]; rfl
  have storeTarget : (C.expand L).target (f.edges (AtomEquality.Same.beforeStore A d)) = [f.ports (.output 0)] := by
    rw [← f.target]; rfl
  obtain ⟨t,u,u',clabel,csrc,ctgt,ht,hu,hu'⟩ := binary_primitive_origin C cert trees compareLabel
    (by intro s; constructor <;> intro h <;> cases h) compareSource compareTarget
  obtain ⟨v,z,ilabel,isrc,itgt,hv,hz⟩ := unary_primitive_origin C cert trees firstLabel
    (by intro s; constructor <;> intro h <;> cases h) firstSource firstTarget
  obtain ⟨v',z',jlabel,jsrc,jtgt,hv',hz'⟩ := unary_primitive_origin C cert trees secondLabel
    (by intro s; constructor <;> intro h <;> cases h) secondSource secondTarget
  obtain ⟨out,o,slabel,ssrc,stgt,hout,ho⟩ := unary_primitive_origin C cert trees storeLabel
    (by intro s; constructor <;> intro h <;> cases h) storeSource storeTarget
  have tEq : t = token := Net.Expansion.host_injective C L (ht.trans attached)
  have vEq : v = u := Net.Expansion.host_injective C L (hv.trans hu.symm)
  have vEq' : v' = u' := Net.Expansion.host_injective C L (hv'.trans hu'.symm)
  subst t; subst v; subst v'
  obtain ⟨S,labels,a,b,rest,entry,entry',nd,boundary,outEq⟩ :=
    atom_two_component C cert trees A tree storeLabel
      (by rw [storeSource]; exact List.mem_cons_self)
      ⟨0,by simp⟩ ⟨1,by simp⟩ (by intro h; have := congrArg Fin.val h; contradiction)
      firstLabel (by rw [firstTarget]; exact List.mem_cons_self)
      secondLabel (by rw [secondTarget]; exact List.mem_cons_self)
  have aEq : a.val = z := Net.Expansion.host_injective C L (entry.trans hz.symm)
  have bEq : b.val = z' := Net.Expansion.host_injective C L (entry'.trans hz'.symm)
  have oEq : S.output = out := Net.Expansion.host_injective C L (outEq.trans hout.symm)
  exact ⟨S,labels,a,b,rest,u,u',o,nd,boundary,clabel,ilabel,jlabel,slabel,csrc,ctgt,
    isrc,aEq ▸ itgt,jsrc,bEq ▸ jtgt,oEq ▸ ssrc,stgt⟩
end Hypernets.Copying.MaximalSharing

import Hypernets.Copying.SharingBinaryOrigin
import Hypernets.Copying.SharingStoreBasinDisjoint
import Hypernets.Copying.AtomEqualityResolution

/-! A false equality match determines two distinct complete atom-sharing
components, with their original stores and selected instance order retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.AtomEquality.Different
open Graph Opening

def leftTreeOccurrence {n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1)) (d : Nat) :
    Occurrence (A.atDepth d) (before A B d) where
  ports := beforeLeftVertex A B d
  internals x := .inr ⟨.tree,x⟩
  edges x := ⟨.tree,x⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

def rightTreeOccurrence {n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1)) (d : Nat) :
    Occurrence (B.atDepth d) (before A B d) where
  ports := beforeRightVertex A B d
  internals x := .inr ⟨.treeRight,x⟩
  edges x := ⟨.treeRight,x⟩
  internal_map _ := rfl
  internal_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj (Sum.inr.inj eq)).2
  edge_injective := by intro a b eq; exact eq_of_heq (Sigma.mk.inj eq).2
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl
end Hypernets.Copying.AtomEquality.Different

namespace Hypernets.Copying.MaximalSharing
open Graph Opening
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- The two original stores force disjoint maximal basins; no independent
assumption on full-tree matching or separation of template holes is required. -/
theorem different_selection {n m} (A : ContractionTree .atom (n+1)) (B : ContractionTree .atom (m+1))
    (f : Occurrence (AtomEquality.Different.before A B d) (C.expand L)) {token : C.Vertex}
    (attached : f.ports (AtomEquality.Different.inputPort n m 0) = Net.Expansion.host C L token) :
    ∃ S U : C.RootedBasin Wire.atom,
      ∃ _leftLabels : ∀ e, S.chosen e → SharingBasin.Eligible C .atom e,
      ∃ _rightLabels : ∀ e, U.chosen e → SharingBasin.Eligible C .atom e,
      ∃ a : S.Vertex, ∃ b : U.Vertex, ∃ rest : List S.Vertex, ∃ rest' : List U.Vertex,
      ∃ u u' o o' : C.Vertex,
        (a::rest).Nodup ∧ (∀ x, x ∈ a::rest ↔ S.Input x) ∧
        (b::rest').Nodup ∧ (∀ x, x ∈ b::rest' ↔ U.Input x) ∧
        C.edgeLabel (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = primitiveLabel d (.operation (.binary .atomEq)) ∧
        C.edgeLabel (f.edges (AtomEquality.Different.beforeLeft A B d)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (AtomEquality.Different.beforeRight A B d)).1 = primitiveLabel d .instanceEdge ∧
        C.edgeLabel (f.edges (AtomEquality.Different.beforeStore A B d)).1 = primitiveLabel d .store ∧
        C.edgeLabel (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 = primitiveLabel d .store ∧
        C.source (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = [token] ∧
        C.target (f.edges ⟨.compare,(0 : Fin 1)⟩).1 = [u,u'] ∧
        C.source (f.edges (AtomEquality.Different.beforeLeft A B d)).1 = [u] ∧
        C.target (f.edges (AtomEquality.Different.beforeLeft A B d)).1 = [a.val] ∧
        C.source (f.edges (AtomEquality.Different.beforeRight A B d)).1 = [u'] ∧
        C.target (f.edges (AtomEquality.Different.beforeRight A B d)).1 = [b.val] ∧
        C.source (f.edges (AtomEquality.Different.beforeStore A B d)).1 = [S.output] ∧
        C.target (f.edges (AtomEquality.Different.beforeStore A B d)).1 = [o] ∧
        C.source (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 = [U.output] ∧
        C.target (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 = [o'] ∧
        (f.edges (AtomEquality.Different.beforeStore A B d)).1 ≠ (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 ∧
        (∀ e, ¬ (S.chosen e ∧ U.chosen e)) := by
  let tree := (AtomEquality.Different.leftTreeOccurrence A B d).comp f
  let tree' := (AtomEquality.Different.rightTreeOccurrence A B d).comp f
  have cl := f.matchEmbedding.primitive ⟨.compare,(0 : Fin 1)⟩ (.operation (.binary .atomEq)) rfl
  have il := f.matchEmbedding.primitive (AtomEquality.Different.beforeLeft A B d) .instanceEdge rfl
  have jl := f.matchEmbedding.primitive (AtomEquality.Different.beforeRight A B d) .instanceEdge rfl
  have sl := f.matchEmbedding.primitive (AtomEquality.Different.beforeStore A B d) .store rfl
  have tl := f.matchEmbedding.primitive (AtomEquality.Different.beforeStoreRight A B d) .store rfl
  change (C.expand L).edgeLabel (f.edges ⟨.compare,(0 : Fin 1)⟩) = _ at cl
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Different.beforeLeft A B d)) = _ at il
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Different.beforeRight A B d)) = _ at jl
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Different.beforeStore A B d)) = _ at sl
  change (C.expand L).edgeLabel (f.edges (AtomEquality.Different.beforeStoreRight A B d)) = _ at tl
  have cs : (C.expand L).source (f.edges ⟨.compare,(0 : Fin 1)⟩) = [f.ports (AtomEquality.Different.inputPort n m 0)] := by
    rw [← f.source]; rfl
  have ct : (C.expand L).target (f.edges ⟨.compare,(0 : Fin 1)⟩) =
      [f.ports (.internal (.inl (0 : Fin 6))),f.ports (.internal (.inl (1 : Fin 6)))] := by
    rw [← f.target]; rfl
  have is : (C.expand L).source (f.edges (AtomEquality.Different.beforeLeft A B d)) = [f.ports (.internal (.inl (0 : Fin 6)))] := by
    rw [← f.source]; rfl
  have it : (C.expand L).target (f.edges (AtomEquality.Different.beforeLeft A B d)) = [tree.ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; rfl
  have js : (C.expand L).source (f.edges (AtomEquality.Different.beforeRight A B d)) = [f.ports (.internal (.inl (1 : Fin 6)))] := by
    rw [← f.source]; rfl
  have jt : (C.expand L).target (f.edges (AtomEquality.Different.beforeRight A B d)) = [tree'.ports (.input ⟨0,by simp⟩)] := by
    rw [← f.target]; rfl
  have ss : (C.expand L).source (f.edges (AtomEquality.Different.beforeStore A B d)) = [tree.ports (.output 0)] := by
    rw [← f.source]; rfl
  have st : (C.expand L).target (f.edges (AtomEquality.Different.beforeStore A B d)) = [f.ports (.output 0)] := by
    rw [← f.target]; rfl
  have ts : (C.expand L).source (f.edges (AtomEquality.Different.beforeStoreRight A B d)) = [tree'.ports (.output 0)] := by
    rw [← f.source]; rfl
  have tt : (C.expand L).target (f.edges (AtomEquality.Different.beforeStoreRight A B d)) = [f.ports (.output 1)] := by
    rw [← f.target]; rfl
  obtain ⟨t,u,u',clabel,csrc,ctgt,ht,hu,hu'⟩ := binary_primitive_origin C cert trees cl
    (by intro s; constructor <;> intro h <;> cases h) cs ct
  obtain ⟨v,z,ilabel,isrc,itgt,hv,hz⟩ := unary_primitive_origin C cert trees il
    (by intro s; constructor <;> intro h <;> cases h) is it
  obtain ⟨v',z',jlabel,jsrc,jtgt,hv',hz'⟩ := unary_primitive_origin C cert trees jl
    (by intro s; constructor <;> intro h <;> cases h) js jt
  obtain ⟨out,o,slabel,ssrc,stgt,hout,ho⟩ := unary_primitive_origin C cert trees sl
    (by intro s; constructor <;> intro h <;> cases h) ss st
  obtain ⟨out',o',tlabel,tsrc,ttgt,hout',ho'⟩ := unary_primitive_origin C cert trees tl
    (by intro s; constructor <;> intro h <;> cases h) ts tt
  have tEq : t = token := Net.Expansion.host_injective C L (ht.trans attached)
  have vEq : v = u := Net.Expansion.host_injective C L (hv.trans hu.symm)
  have vEq' : v' = u' := Net.Expansion.host_injective C L (hv'.trans hu'.symm)
  subst t; subst v; subst v'
  obtain ⟨S,labels,a,rest,entry,nd,boundary,outEq⟩ := atom_component C cert trees A tree sl
    (by rw [ss]; exact List.mem_cons_self) ⟨0,by simp⟩ il
    (by rw [it]; exact List.mem_cons_self)
  obtain ⟨U,labels',b,rest',entry',nd',boundary',outEq'⟩ := atom_component C cert trees B tree' tl
    (by rw [ts]; exact List.mem_cons_self) ⟨0,by simp⟩ jl
    (by rw [jt]; exact List.mem_cons_self)
  have aEq : a.val = z := Net.Expansion.host_injective C L (entry.trans hz.symm)
  have bEq : b.val = z' := Net.Expansion.host_injective C L (entry'.trans hz'.symm)
  have oEq : S.output = out := Net.Expansion.host_injective C L (outEq.trans hout.symm)
  have oEq' : U.output = out' := Net.Expansion.host_injective C L (outEq'.trans hout'.symm)
  have different : (f.edges (AtomEquality.Different.beforeStore A B d)).1 ≠
      (f.edges (AtomEquality.Different.beforeStoreRight A B d)).1 := by
    intro eq
    have same := SharingRootOrigin.retained_owner_injective C cert trees sl
      (by intro s; constructor <;> intro h <;> cases h) eq
    have bad := congrArg Sigma.fst (f.edge_injective same)
    cases bad
  have disjoint := SharingBasin.stores_disjoint C S U labels labels' slabel tlabel
    (by rw [ssrc,← oEq]; exact List.mem_cons_self)
    (by rw [tsrc,← oEq']; exact List.mem_cons_self) different
  exact ⟨S,U,labels,labels',a,b,rest,rest',u,u',o,o',nd,boundary,nd',boundary',
    clabel,ilabel,jlabel,slabel,tlabel,csrc,ctgt,isrc,aEq ▸ itgt,jsrc,bEq ▸ jtgt,
    oEq ▸ ssrc,stgt,oEq' ▸ tsrc,ttgt,different,disjoint⟩
end Hypernets.Copying.MaximalSharing

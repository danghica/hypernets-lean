import Hypernets.Copying.SharingTreePair
import Hypernets.Copying.SharingBasin

/-! Actual sharing roots and maximal-component provenance in original paired
contexts. Store and operation heads are retained because sharing templates
cannot introduce those labels. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.SharingRootOrigin
open Graph Search.Expansion
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (trees : T.SharingTrees)
include cert trees

/-- An actual primitive which is neither weakening nor contraction must
belong to a retained original context edge. -/
theorem retained {e : (C.expand L).Edge} {p : Primitive}
    (label : (C.expand L).edgeLabel e = primitiveLabel d p)
    (nonsharing : ∀ s, p ≠ .weakening s ∧ p ≠ .contraction s) :
    Nonempty (Retained C L e.1) := by
  rcases (cert e.1).origin with retained | ⟨h,hole,pair⟩
  · exact retained.1
  · obtain ⟨s,n,_,_,left,_⟩ := (trees pair).shape
    have actual := left e.2
    change (L e.1).edgeLabel e.2 = primitiveLabel d p at label
    rcases actual with actual | actual
    · exact False.elim ((nonsharing s).1 (primitiveLabel_injective d (label.symm.trans actual)))
    · exact False.elim ((nonsharing s).2 (primitiveLabel_injective d (label.symm.trans actual)))

/-- Actual sharing edges have sharing-like original owners, including the
entire typed original hole when the edge lies inside a template filling. -/
theorem sharing_owner {s : ShareSort} {e : (C.expand L).Edge}
    (label : (C.expand L).edgeLabel e = primitiveLabel d (.weakening s) ∨
      (C.expand L).edgeLabel e = primitiveLabel d (.contraction s)) :
    SharingLabel d s (C.edgeLabel e.1) := by
  rcases (cert e.1).origin with ⟨⟨copy⟩,_⟩ | ⟨h,hole,pair⟩
  · rcases label with label | label
    · exact .inl ((copy.primitive _).mp (by change (L e.1).edgeLabel e.2 = _ at label; simpa only [copy.only e.2] using label))
    · exact .inr (.inl ((copy.primitive _).mp (by change (L e.1).edgeLabel e.2 = _ at label; simpa only [copy.only e.2] using label)))
  · obtain ⟨t,n,input,output,left,_⟩ := (trees pair).shape
    have same : t = s := by
      have actual := left e.2
      rcases actual with actual | actual <;> rcases label with label | label
      all_goals have eq := primitiveLabel_injective d (actual.symm.trans label)
      all_goals cases eq <;> rfl
    subst t
    refine .inr (.inr ⟨h,n,hole,?_,?_⟩)
    · simpa only [hole,primitive_input,primitiveSignature] using input
    · simpa only [hole,primitive_output,primitiveSignature] using output

omit cert trees in
/-- A retained actual source is exactly the image of an original context source. -/
theorem source_origin {e : (C.expand L).Edge} (copy : Retained C L e.1) {w}
    (source : w ∈ (C.expand L).source e) :
    ∃ v, v ∈ C.source e.1 ∧ Net.Expansion.host C L v = w := by
  have eq : (C.expand L).source e = (C.source e.1).map (Net.Expansion.host C L) := by
    rcases e with ⟨e,x⟩
    simpa only [copy.only x] using copy.source_eq
  rw [eq] at source
  exact List.mem_map.mp source

/-- A genuine sharing root feeding a store or an operation head determines
its original host root, output coordinate, and maximal-basin terminal law. -/
theorem root {s : ShareSort} {e a : (C.expand L).Edge} {p : Primitive} {w}
    (sharing : (C.expand L).edgeLabel e = primitiveLabel d (.weakening s) ∨
      (C.expand L).edgeLabel e = primitiveLabel d (.contraction s))
    (target : w ∈ (C.expand L).target e)
    (head : (C.expand L).edgeLabel a = primitiveLabel d p)
    (source : w ∈ (C.expand L).source a)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (notHole : ∀ h, p ≠ .hole h) :
    ∃ v, Net.Expansion.host C L v = w ∧
      SharingLabel d s (C.edgeLabel e.1) ∧ C.target e.1 = [v] ∧
      ∀ b, SharingLabel d s (C.edgeLabel b) → ¬ C.Adjacent e.1 b := by
  obtain ⟨copy⟩ := retained C cert trees head nonsharing
  obtain ⟨v,oldSource,eq⟩ := source_origin C copy source
  have oldTarget : v ∈ C.target e.1 := Search.Expansion.target_owner C L (eq.symm ▸ target)
  have owner := sharing_owner C cert trees sharing
  have single : (C.target e.1).length = 1 := by rw [C.target_length,owner.target]; rfl
  obtain ⟨v',targets⟩ := List.length_eq_one_iff.mp single
  have equal : v = v' := by simpa only [targets,List.mem_singleton] using oldTarget
  subst v'
  refine ⟨v,eq,owner,targets,?_⟩
  intro b eligible ⟨x,xt,xs⟩
  have equal : x = v := by simpa only [targets,List.mem_singleton] using xt
  subst x
  have same := C.source_unique xs oldSource
  subst b
  have oldHead : C.edgeLabel a.1 = primitiveLabel d p :=
    (copy.primitive p).mp (by change (L a.1).edgeLabel a.2 = _ at head; simpa only [copy.only a.2] using head)
  rcases eligible with weak | contraction | ⟨h,n,hole,_,_⟩
  · exact (nonsharing s).1 (primitiveLabel_injective d (oldHead.symm.trans weak))
  · exact (nonsharing s).2 (primitiveLabel_injective d (oldHead.symm.trans contraction))
  · exact notHole h (primitiveLabel_injective d (oldHead.symm.trans hole))

/-- Sharing-only actual traces project to sharing-only original-owner traces;
steps wholly inside one filled tree become zero steps. -/
theorem owner_trace {s : ShareSort} {a b : (C.expand L).Edge} {n}
    (path : Trace (fun x y : (C.expand L).Edge =>
      ((C.expand L).edgeLabel x = primitiveLabel d (.weakening s) ∨
        (C.expand L).edgeLabel x = primitiveLabel d (.contraction s)) ∧
      (C.expand L).Adjacent x y ∧
      ((C.expand L).edgeLabel y = primitiveLabel d (.weakening s) ∨
        (C.expand L).edgeLabel y = primitiveLabel d (.contraction s))) a b n) :
    ∃ k, Trace (C.SharingNext (SharingBasin.Eligible C s)) a.1 b.1 k := by
  induction path with
  | refl a => exact ⟨0,.refl _⟩
  | @step a b c n link path ih =>
    obtain ⟨k,tail⟩ := ih
    by_cases eq : a.1 = b.1
    · exact ⟨k,eq ▸ tail⟩
    · exact ⟨k+1,.step ⟨sharing_owner C cert trees link.1,
        Net.Expansion.adjacent_cross C L eq a.2 b.2 link.2.1,
        sharing_owner C cert trees link.2.2⟩ tail⟩

omit cert trees in
/-- Primitive labels of a complete matched contraction tree are preserved
on every actual expanded edge. -/
theorem tree_labels {s : ShareSort} {m : Nat} (A : ContractionTree s m)
    (f : Opening.Occurrence (A.atDepth d) (C.expand L)) (e : A.net.Edge) :
    (C.expand L).edgeLabel (f.edges e) = primitiveLabel d (.weakening s) ∨
      (C.expand L).edgeLabel (f.edges e) = primitiveLabel d (.contraction s) := by
  rcases A.labels e with label | label
  · exact .inl (f.matchEmbedding.primitive e _ (congrArg (primitiveLabel d) label))
  · exact .inr (f.matchEmbedding.primitive e _ (congrArg (primitiveLabel d) label))

/-- Apply original-root extraction to the actual output of an arbitrary
complete sharing-tree occurrence, attached to a real nonsharing consumer. -/
theorem tree_root {s : ShareSort} {m : Nat} (A : ContractionTree s m)
    (f : Opening.Occurrence (A.atDepth d) (C.expand L))
    {a : (C.expand L).Edge} {p : Primitive}
    (head : (C.expand L).edgeLabel a = primitiveLabel d p)
    (source : f.ports (.output 0) ∈ (C.expand L).source a)
    (nonsharing : ∀ t, p ≠ .weakening t ∧ p ≠ .contraction t)
    (notHole : ∀ h, p ≠ .hole h) :
    ∃ v, Net.Expansion.host C L v = f.ports (.output 0) ∧
      SharingLabel d s (C.edgeLabel (f.edges A.root).1) ∧
      C.target (f.edges A.root).1 = [v] ∧
      ∀ b, SharingLabel d s (C.edgeLabel b) → ¬ C.Adjacent (f.edges A.root).1 b :=
  root C cert trees (tree_labels C A f A.root) (f.matchEmbedding.target_mem A.root_output)
    head source nonsharing notHole

/-- Every edge of an actual matched tree has its owner in the original
maximal sharing predecessor component. Unused branches are included. -/
theorem tree_selected {s : ShareSort} {m : Nat} (A : ContractionTree s m)
    (f : Opening.Occurrence (A.atDepth d) (C.expand L)) :
    ∀ e, C.PredecessorOf (SharingBasin.Eligible C s) (f.edges A.root).1 (f.edges e).1 := by
  have labels := tree_labels C A f
  intro e
  obtain ⟨n,path⟩ := A.reaches_root e
  refine ⟨sharing_owner C cert trees (labels e),?_⟩
  apply owner_trace C cert trees
  exact path.map f.edges (fun {a b} adj => ⟨labels a,f.matchEmbedding.adjacent adj,labels b⟩)

end Hypernets.Copying.SharingRootOrigin

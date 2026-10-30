import Hypernets.Copying.SharingTreePair

/-! A selected maximal sharing context yields two actual contraction trees
and an original-template residual certificate, without flattening hole pairs
into arbitrary tree equations. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace LabelCopy
/-- A literal corolla has no edge adjacency, since all targets are outputs
and all sources are inputs. This remains true for arbitrary carrier names. -/
theorem no_adjacency {d I O} {G : Hypernet d I O} {label} (c : LabelCopy G label)
    {e f : G.Edge} : ¬ G.Adjacent e f := by
  rintro ⟨v,target,source⟩
  rw [c.only e,c.target] at target
  rw [c.only f,c.source] at source
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp target
  obtain ⟨j,_,eq⟩ := List.mem_map.mp source
  cases eq

theorem acyclic {d I O} {G : Hypernet d I O} {label} (c : LabelCopy G label) :
    ∀ {es}, G.Path es → es.Nodup := by
  intro es path
  cases path with
  | single => simp
  | cons adj _ => exact False.elim (c.no_adjacency adj)
end LabelCopy

namespace SharingTreePair
/-- Carrier-renamed sharing trees remain acyclic on both actual endpoints. -/
theorem acyclic {d I O} {G H : Hypernet d I O} (pair : SharingTreePair G H) :
    (∀ {es}, G.Path es → es.Nodup) ∧ (∀ {es}, H.Path es → es.Nodup) := by
  cases pair with
  | trees T U f g =>
    exact ⟨((T.sharingTreeGraph _).iso f.symm).acyclic,((U.sharingTreeGraph _).iso g).acyclic⟩
end SharingTreePair

namespace SharingTreeContext
variable {s : ShareSort} {m d : Nat} (C : SharingTreeContext s m d)

/-- The sole output type of every context label is the enclosing sharing sort. -/
theorem label_output (e : C.net.Edge) :
    (alphabet d).signature.output (C.net.edgeLabel e) = [s.wire] := by
  rcases C.labels e with eq | eq | ⟨h,n,eq,_,output⟩
  · rw [eq,primitive_output]; rfl
  · rw [eq,primitive_output]; rfl
  · rw [eq,primitive_output]; exact output

/-- Sharing primitives and holes are all focus-free. -/
theorem focusFree : FocusFree C.net := by
  intro e
  rcases C.labels e with eq | eq | ⟨h,n,eq,_,_⟩
  all_goals rw [eq]
  all_goals cases d <;> intro mode bad <;> cases bad

variable {T : PreTemplate}
    {L R : (e : C.net.Edge) → Hypernet d ((alphabet d).signature.input (C.net.edgeLabel e))
      ((alphabet d).signature.output (C.net.edgeLabel e))}
    (cert : ∀ e, DeepFillingEdge T C.net L R e) (trees : T.SharingTrees)
    (closed : HoleFree (C.net.expand L))
include cert trees closed

/-- Each original selected slot expands to acyclic same-sort sharing edges.
A retained unfilled hole is excluded by the actual closed left expansion. -/
theorem filling_shapes (e : C.net.Edge) :
    ((∀ a, (L e).edgeLabel a = primitiveLabel d (.weakening s) ∨
        (L e).edgeLabel a = primitiveLabel d (.contraction s)) ∧
      (∀ {es}, (L e).Path es → es.Nodup)) ∧
    ((∀ a, (R e).edgeLabel a = primitiveLabel d (.weakening s) ∨
        (R e).edgeLabel a = primitiveLabel d (.contraction s)) ∧
      (∀ {es}, (R e).Path es → es.Nodup)) := by
  cases cert e with
  | retained l r =>
    have labels : C.net.edgeLabel e = primitiveLabel d (.weakening s) ∨
        C.net.edgeLabel e = primitiveLabel d (.contraction s) := by
      rcases C.labels e with eq | eq | ⟨h,n,eq,_,_⟩
      · exact .inl eq
      · exact .inr eq
      · have bad := closed ⟨e,l.edge⟩
        change LabelAll (fun p => ∀ h, p ≠ .hole h) d ((L e).edgeLabel l.edge) at bad
        rw [l.edge_label,eq] at bad
        cases d <;> exact False.elim (bad h rfl)
    refine ⟨⟨?_,l.acyclic⟩,⟨?_,r.acyclic⟩⟩
    · intro a; rw [l.only a,l.edge_label]; exact labels
    · intro a; rw [r.only a,r.edge_label]; exact labels
  | filled h label pair =>
    obtain ⟨t,n,_,output,left,right⟩ := (trees pair).shape
    have sort : t = s := by
      have eq := output.symm.trans (C.label_output e)
      have wire := List.cons.inj eq |>.1
      cases t <;> cases s <;> simp_all [ShareSort.wire]
    subst t
    exact ⟨⟨left,(trees pair).acyclic.1⟩,⟨right,(trees pair).acyclic.2⟩⟩
  | boxed b label inner l r =>
    rcases C.labels e with eq | eq | ⟨h,n,eq,_,_⟩
    all_goals rw [label] at eq; cases eq

/-- The left expansion is a genuine concrete sharing tree. -/
theorem left_sharingTreeGraph : SharingTreeGraph s m (C.net.expand L) :=
  C.expandedTree L (fun e => (C.filling_shapes cert trees closed e).1.1)
    (fun e => (C.filling_shapes cert trees closed e).1.2)

/-- The right expansion has the same ordered boundary and sharing sort. -/
theorem right_sharingTreeGraph : SharingTreeGraph s m (C.net.expand R) :=
  C.expandedTree R (fun e => (C.filling_shapes cert trees closed e).2.1)
    (fun e => (C.filling_shapes cert trees closed e).2.2)

/-- Normalizing the expanded graphs to primitive trees preserves the original
common context and every original template relation, with identity token maps. -/
noncomputable def treeWitness : FillingWitness T
    ((C.left_sharingTreeGraph cert trees closed).tree.atDepth d)
    ((C.right_sharingTreeGraph cert trees closed).tree.atDepth d) where
  context := C.net
  free := C.focusFree
  left := L
  right := R
  edges := cert
  leftIso := (C.left_sharingTreeGraph cert trees closed).treeIso.symm
  rightIso := (C.right_sharingTreeGraph cert trees closed).treeIso.symm

end SharingTreeContext
end Hypernets.Copying

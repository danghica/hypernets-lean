import Hypernets.Copying.AssignmentRetainedCanonical
import Hypernets.Copying.LambdaEntryAssignmentSelection

/-! Assignment residuals preserve the full original paired filling, including
stable lambda values inside shallow families. Only the retained assignment
head and the two source-determined target attachments change. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.LambdaEntryOverlap
open Graph Combined Search.Expansion MatchEmbedding
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e)

include cert in
/-- The assignment head at an original token is retained even when its new
value belongs to a shallow lambda family. -/
theorem assignment_head (heads : T.LambdaEntries) {v : C.Vertex} {e : (C.expand L).Edge}
    (head : HeadAt (C.expand L) (Net.Expansion.host C L v) e
      (.operation (.binary .assign))) :
    HeadAt C v e.1 (.operation (.binary .assign)) := by
  obtain ⟨copy⟩ := source_retained C cert heads head.2 (by
    rw [head.1]; intro eq; cases primitiveLabel_injective d eq)
  exact ⟨retained_primitive C copy head.1,source_owner C L head.2⟩

/-- An original primitive head appears at the identical original token in
both expansions. The statement preserves actual edge representatives. -/
theorem primitive_head_expanded {v : C.Vertex} {e : C.Edge} {p : Primitive}
    (head : HeadAt C v e p)
    (copy : LabelCopy (L e) (C.edgeLabel e)) :
    HeadAt (C.expand L) (Net.Expansion.host C L v) ⟨e,copy.edge⟩ p := by
  refine ⟨copy.edge_label.trans head.1,?_⟩
  have row : (C.expand L).source ⟨e,copy.edge⟩ = (C.source e).map (Net.Expansion.host C L) := by
    simpa only [LabelCopy.retained] using copy.retained.source_eq
  rw [row]
  exact List.mem_map_of_mem head.2

/-- A retained edge with a fixed original owner is the unique edge of its
literal corolla copy. -/
theorem retained_edge_eq {F} {e : C.Edge} (copy : LabelCopy (F e) (C.edgeLabel e))
    (x : (C.expand F).Edge) (owner : x.1 = e) : x = ⟨e,copy.edge⟩ := by
  obtain ⟨a,b⟩ := x
  dsimp only at owner
  subst a
  exact congrArg (Sigma.mk e) (copy.only b)

include cert in
/-- Any two actual opposite assignment successors are related by the
original template. The original common match is identified by source
uniqueness; neither stable argument is replaced by an assumed equivalence. -/
theorem assignment_successor_pointed (heads : T.LambdaEntries)
    (reverseHeads : T.converse.LambdaEntries) (free : FocusFree C)
    {v : C.Vertex} {e : C.Edge}
    (head : HeadAt C v e (.operation (.binary .assign)))
    {G H : Hypernet d I O} {u : G.Vertex} {w : H.Vertex}
    (left : Rewrite (C.expand L) (Net.Expansion.host C L v) G u)
    (right : Rewrite (C.expand R) (Net.Expansion.host C R v) H w) :
    Nonempty (BoxPullWeakening.PointedWitness T G u H w) := by
  obtain ⟨l,r⟩ := (cert e).primitive_copies head.1 (by intro h eq; cases eq)
  obtain ⟨a⟩ := rewrite_assignment_match left (primitive_head_expanded C head l)
  obtain ⟨b⟩ := rewrite_assignment_match right (primitive_head_expanded C head r)
  obtain ⟨q,qhead,_,_,_,qnew,qold⟩ := assignment_match_owner C cert heads a
  obtain ⟨q',qhead',_,_,_,qnew',qold'⟩ :=
    assignment_match_owner C (fun e => (cert e).converse) reverseHeads b
  have same := Assignment.Match.unique q q'
  subst q'
  obtain ⟨lc,rc⟩ := (cert q.headEdge).primitive_copies q.head.1 (by intro h eq; cases eq)
  have paired := Assignment.Retained.pointed C q cert free a b lc rc
    (retained_edge_eq C lc a.headEdge qhead.symm)
    (retained_edge_eq C rc b.headEdge qhead'.symm)
    qnew.symm qold.symm qnew'.symm qold'.symm
  obtain ⟨li⟩ := rewrite_assignment_canonical left a
  obtain ⟨ri⟩ := rewrite_assignment_canonical right b
  have result := paired.congr li.graph ri.graph
  exact ⟨by simpa only [li.vertex,ri.vertex] using result⟩

end Hypernets.Copying.LambdaEntryOverlap

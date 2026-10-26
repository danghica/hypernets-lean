import Hypernets.Copying.ReplacementStates

/-! Canonical allocation successors for arbitrary contextual matches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Successive changes of interface proofs compose without changing the graph. -/
theorem reboundary_comp {d I O J K L M} (G : Hypernet d I O)
    (hi : I = J) (ho : O = K) (hj : J = L) (hk : K = M) :
    (G.reboundary hi ho).reboundary hj hk = G.reboundary (hi.trans hj) (ho.trans hk) := by
  cases hi; cases ho; cases hj; cases hk; simp only [Net.reboundary_refl]

namespace Allocation
/-- The selected ref occurrence in the unreduced allocation graph. -/
def head {d O} (G : Hypernet d [.term] O) : (before G).Edge :=
  Serial.leftEdge _ _ (by cases d <;> exact (0 : Fin 1))

theorem head_at {d O} (G : Hypernet d [.term] O) :
    MatchEmbedding.HeadAt (before G) (.input 0) (head G) (.operation (.unary .ref)) := by
  cases d <;> exact ⟨rfl,List.mem_cons_self⟩

/-- Allocate at one ref edge; the interface equalities are forced by its label. -/
def filler {d I O} (G : Hypernet d I O) (e : G.Edge)
    (label : G.edgeLabel e = primitiveLabel d (.operation (.unary .ref))) :
    Hypernet d ((alphabet d).signature.input (G.edgeLabel e))
      ((alphabet d).signature.output (G.edgeLabel e)) :=
  (cellPrefix d).reboundary (by rw [label,primitive_input]; rfl)
    (by rw [label,primitive_output]; rfl)

/-- A canonical successor depends only on the source graph, selected edge and token. -/
noncomputable def canonical {d I O} (G : Hypernet d I O) (e : G.Edge)
    (label : G.edgeLabel e = primitiveLabel d (.operation (.unary .ref))) (v : G.Vertex) : Combined.State d I O :=
  Combined.Replacement.state G e (filler G e label) v

/-- Canonical allocation is equivariant for recursive renaming of the whole host. -/
noncomputable def canonical_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H)
    (e : G.Edge) (label : G.edgeLabel e = primitiveLabel d (.operation (.unary .ref))) (v : G.Vertex) :
    Combined.StateIso (canonical G e label v)
      (canonical H (f.edges.toFun e) ((Search.primitive_equiv (f.edge_label e) _).mp label)
        (Port.map f.vertices.toFun v)) := by
  have eq : (filler G e label).reboundary (labelEquiv_input d (f.edge_label e))
      (labelEquiv_output d (f.edge_label e)) =
      filler H (f.edges.toFun e) ((Search.primitive_equiv (f.edge_label e) _).mp label) := by
    unfold filler; rw [reboundary_comp]
  exact (Combined.Replacement.rename f e (filler G e label) v).trans
    (Combined.StateIso.ofEq (congrArg (fun A => Combined.Replacement.state H (f.edges.toFun e) A
      (Port.map f.vertices.toFun v)) eq))

/-- The local allocation result is exactly replacement of its ref edge, up to graph representation. -/
noncomputable def canonical_local {d O} (G : Hypernet d [.term] O) :
    Combined.StateIso (canonical (before G) (head G) (head_at G).1 (.input 0))
      ⟨after G,(.search,.input 0)⟩ := by
  cases d with
  | zero =>
    refine ⟨?_,rfl,rfl⟩
    exact (DeepIso.ofIso (Serial.plug_left (primitiveNet 0 (.operation (.unary .ref))) G (0 : Fin 1) (cellPrefix 0))).trans
      (Serial.congr (DeepIso.ofIso (Net.corolla_plug_iso (primitiveLabel 0 (.operation (.unary .ref))) (cellPrefix 0))) (DeepIso.refl G))
  | succ d =>
    refine ⟨?_,rfl,rfl⟩
    exact (DeepIso.ofIso (Serial.plug_left (primitiveNet (d+1) (.operation (.unary .ref))) G (0 : Fin 1) (cellPrefix (d+1)))).trans
      (Serial.congr (DeepIso.ofIso (Net.corolla_plug_iso (primitiveLabel (d+1) (.operation (.unary .ref))) (cellPrefix (d+1)))) (DeepIso.refl G))
end Allocation
end Hypernets.Copying

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- If a contextual rewrite is focused at a primitive head, its changed component
contains that very head. No assumption about an injective boundary map is needed. -/
theorem rewrite_head_reflect {d r I O J K} {G H : Hypernet d I O} {N : Hypernet r J K}
    {v w a p} (step : Rewrite G v H w) (f : MatchEmbedding G N)
    (head : HeadAt N (f.ports v) a p) : ∃ e, HeadAt G v e p ∧ f.edges e = a := by
  obtain ⟨c,e,chosen,_⟩ := rewrite_recognizes step
  obtain ⟨edge,label⟩ := head_unique (f.head chosen) head
  exact ⟨e,label ▸ chosen,edge⟩

/-- Among actual local rules, a ref head has precisely the canonical allocation successor. -/
theorem local_allocation_canonical {d I O} {G H : Hypernet d I O} {v w e}
    (step : Local G v H w) (head : HeadAt G v e (.operation (.unary .ref))) :
    Nonempty (StateIso (Allocation.canonical G e head.1 v) ⟨H,(.search,w)⟩) := by
  cases step with
  | allocate A stable =>
    have eq := (head_unique head (Allocation.head_at A)).1
    subst e
    exact ⟨Allocation.canonical_local A⟩
  | read T d =>
    have bad := (head_unique head (show HeadAt (Dereference.before T d) _ ⟨.reader,(0 : Fin 1)⟩
      (.operation (.unary .deref)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | @assign d h O T A stable =>
    cases d
    all_goals
      have bad := (head_unique head (show HeadAt (Assignment.before T A) _ ⟨.assign,(0 : Fin 1)⟩
        (.operation (.binary .assign)) from ⟨rfl,List.mem_cons_self⟩)).2
      cases bad
  | same T d =>
    have bad := (head_unique head (show HeadAt (AtomEquality.Same.before T d) _ ⟨.compare,(0 : Fin 1)⟩
      (.operation (.binary .atomEq)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | different T U d =>
    have bad := (head_unique head (show HeadAt (AtomEquality.Different.before T U d) _ ⟨.compare,(0 : Fin 1)⟩
      (.operation (.binary .atomEq)) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | beta B A stable =>
    have bad := (head_unique head (show HeadAt (Application.before B A) _ ⟨false,(0 : Fin 1)⟩
      (.operation .app) from ⟨rfl,List.mem_cons_self⟩)).2
    cases bad
  | copy T A copyable =>
    obtain ⟨a,chosen⟩ := CopyRule.before_active_head T A ⟨0,by simp⟩
    cases (head_unique head chosen).2
  | unaryArithmetic d n => cases (head_unique head (Arithmetic.unary_head d n)).2
  | binaryArithmetic o d m n => cases (head_unique head (Arithmetic.binary_head o d m n)).2

/-- Every contextual allocation match, regardless of its decomposition, produces
the canonical edge replacement with exactly the same resumed token. -/
theorem rewrite_allocation_canonical {d I O} {G H : Hypernet d I O} {v w e}
    (step : Rewrite G v H w) (head : HeadAt G v e (.operation (.unary .ref))) :
    Nonempty (StateIso (Allocation.canonical G e head.1 v) ⟨H,(.search,w)⟩) := by
  induction step with
  | «local» step => exact local_allocation_canonical step head
  | @rename I O G H G' H' v w f g step ih =>
    obtain ⟨a,inner,eq⟩ := rewrite_head_reflect step (MatchEmbedding.ofDeepIso f) head
    obtain ⟨result⟩ := ih inner
    subst e
    exact ⟨(Allocation.canonical_rename f a inner.1 v).symm.trans
      (result.trans ⟨g,rfl,rfl⟩)⟩
  | @plug I O C hole G H v w step ih =>
    obtain ⟨a,inner,eq⟩ := rewrite_head_reflect step (MatchEmbedding.plug C hole G) head
    obtain ⟨result⟩ := ih inner
    subst e
    exact ⟨(Replacement.plug C hole G a (Allocation.filler G a inner.1) v).trans
      (StateIso.plug C hole result)⟩
  | @expand I O C F K hole others v w step ih =>
    obtain ⟨a,inner,eq⟩ := rewrite_head_reflect step (MatchEmbedding.expand C F hole) head
    obtain ⟨result⟩ := ih inner
    subst e
    exact ⟨Replacement.expand_result C F K hole others a (Allocation.filler (F hole) a inner.1) v w result⟩

/-- Independently selected allocation rewrites have recursively isomorphic successor states. -/
theorem allocation_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u e}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  obtain ⟨f⟩ := rewrite_allocation_canonical first head
  obtain ⟨g⟩ := rewrite_allocation_canonical second head
  exact ⟨f.symm.trans g⟩
end Hypernets.Copying.Combined

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- A full-machine step at an allocation request has the canonical successor.
The search alternative is excluded by the existing search-mode rules. -/
theorem allocation_step_canonical {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.unary .ref))) (step : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso (Allocation.canonical G e head.1 v) t) := by
  cases step with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | rewrite h => exact rewrite_allocation_canonical h head

/-- Full-machine successor coherence at every allocation request, with no determinism premise. -/
theorem allocation_step_deterministic {d I O} {G : Hypernet d I O} {v e} {s t : State d I O}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso s t) := by
  obtain ⟨f⟩ := allocation_step_canonical head first
  obtain ⟨g⟩ := allocation_step_canonical head second
  exact ⟨f.symm.trans g⟩

/-- Every admitted allocation can execute directly to its canonical representative. -/
theorem allocation_step_to_canonical {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.unary .ref))) (step : Step ⟨G,(.rewrite,v)⟩ t) :
    Step ⟨G,(.rewrite,v)⟩ (Allocation.canonical G e head.1 v) := by
  cases step with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | @rewrite G H v w h =>
    obtain ⟨iso⟩ := rewrite_allocation_canonical h head
    have moved := Rewrite.rename (DeepIso.refl G) iso.symm.graph h
    have eq := iso.symm.vertex
    change Port.map iso.symm.graph.vertices.toFun w = _ at eq
    change Step ⟨G,(.rewrite,v)⟩ ⟨(Allocation.canonical G e head.1 v).1,
      (.search,(Allocation.canonical G e head.1 v).2.2)⟩
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id,eq] using Step.rewrite moved

/-- Allocating consumes exactly one step, independently of the chosen match.
All subsequent successful costs, including those through arbitrary callbacks, agree. -/
theorem allocation_cost_iff {d I O} {G : Hypernet d I O} {v e} {t : State d I O}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn (n+1) ⟨G,(.rewrite,v)⟩ ↔ TerminatesIn n t := by
  constructor
  · rintro ⟨u,run,done⟩
    cases run with
    | cons first rest =>
      obtain ⟨iso⟩ := allocation_step_deterministic head first step
      exact (terminatesIn_iso iso n).mp ⟨u,rest,done⟩
  · rintro ⟨u,run,done⟩
    exact ⟨u,.cons step run,done⟩

/-- Allowance-indexed unbounded execution inherits allocation successor coherence. -/
theorem allocation_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    Represents s t := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      obtain ⟨iso⟩ := allocation_step_deterministic head first second
      exact .lift iso

/-- Independently chosen unbounded allocation successors agree for every cost preorder. -/
theorem allocation_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v e} {s t : UnboundedState}
    (head : HeadAt G v e (.operation (.unary .ref)))
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t :=
  represents_equiv Q (allocation_unbounded_deterministic head first second)
end Hypernets.Copying.Combined

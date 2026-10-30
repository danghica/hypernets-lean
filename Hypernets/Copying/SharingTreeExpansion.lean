import Hypernets.Copying.MinimalContractionSpine
import Hypernets.Graph.ExpansionAdjacency

/-! Simultaneous substitution preserves finite sharing trees.  The proof uses
actual path acyclicity of both the context and every inserted graph. -/
namespace Hypernets.Copying
open Graph
namespace SharingTreeExpansion
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O : List L}

/-- Terminal distance in a finite acyclic graph with functional adjacency. -/
noncomputable def distance (G : Net σ I O)
    (acyclic : ∀ {es}, G.Path es → es.Nodup) (e : G.Edge) : Nat :=
  Classical.choose (Classical.choose_spec (G.exists_terminal_trace acyclic e))

theorem distance_spec (G : Net σ I O)
    (acyclic : ∀ {es}, G.Path es → es.Nodup) (e : G.Edge) :
    ∃ f, Trace G.Adjacent e f (distance G acyclic e) ∧ Terminal G.Adjacent f := by
  exact ⟨_, Classical.choose_spec (Classical.choose_spec (G.exists_terminal_trace acyclic e))⟩

/-- A forward adjacency consumes precisely one unit of terminal distance. -/
theorem distance_step (G : Net σ I O)
    (acyclic : ∀ {es}, G.Path es → es.Nodup)
    (single : ∀ e, (G.target e).length = 1) {e f : G.Edge} (adj : G.Adjacent e f) :
    distance G acyclic e = distance G acyclic f + 1 := by
  obtain ⟨a,p,pa⟩ := distance_spec G acyclic e
  obtain ⟨b,q,qb⟩ := distance_spec G acyclic f
  exact (Trace.terminal_unique (R := G.Adjacent) (fun {a b c} h h' => G.adjacent_functional_at (single a) h h')
    p (.step adj q) pa qb).2

private def LexLess (a b : Nat × Nat) : Prop :=
  a.1 < b.1 ∨ a.1 = b.1 ∧ a.2 < b.2

private theorem lex_trans {a b c : Nat × Nat} (ab : LexLess a b) (bc : LexLess b c) :
    LexLess a c := by
  rcases ab with ab | ⟨ab,ab'⟩ <;> rcases bc with bc | ⟨bc,bc'⟩
  · exact .inl (Nat.lt_trans ab bc)
  · exact .inl (bc ▸ ab)
  · exact .inl (ab ▸ bc)
  · exact .inr ⟨ab.trans bc,Nat.lt_trans ab' bc'⟩

private theorem lex_irrefl (a : Nat × Nat) : ¬ LexLess a a := by
  simp [LexLess]

/-- An acyclic one-target host remains acyclic after replacing its edges by
acyclic one-target graphs. No global ordering of graph carriers is assumed. -/
theorem acyclic_expand (C : Net σ I O)
    (H : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))
    (hostAcyclic : ∀ {es}, C.Path es → es.Nodup)
    (hostSingle : ∀ e, (C.target e).length = 1)
    (localAcyclic : ∀ e {es}, (H e).Path es → es.Nodup)
    (localSingle : ∀ e f, ((H e).target f).length = 1) :
    ∀ {es}, (C.expand H).Path es → es.Nodup := by
  let rank (e : (C.expand H).Edge) :=
    (distance C hostAcyclic e.1,distance (H e.1) (localAcyclic e.1) e.2)
  have decreasing : ∀ {a b : (C.expand H).Edge}, (C.expand H).Adjacent a b →
      LexLess (rank b) (rank a) := by
    rintro ⟨e,a⟩ ⟨f,b⟩ adj
    by_cases eq : e = f
    · subst f
      have noLoop : Net.Replacement.NonSelfLoop C e := by
        intro v source target
        have bad := hostAcyclic (.cons ⟨v,target,source⟩ (.single e))
        simp at bad
      have localAdj := (Net.Expansion.adjacent_same_iff C H e noLoop a b).mp adj
      have h := distance_step (H e) (localAcyclic e) (localSingle e) localAdj
      exact .inr ⟨rfl,by change distance (H e) (localAcyclic e) b < distance (H e) (localAcyclic e) a; omega⟩
    · have h := distance_step C hostAcyclic hostSingle
        (Net.Expansion.adjacent_cross C H eq a b adj)
      exact .inl (by change distance C hostAcyclic f < distance C hostAcyclic e; omega)
  intro es path
  have pairwise : es.Pairwise (fun a b => LexLess (rank b) (rank a)) := by
    induction path with
    | single e => simp
    | @cons e f es adjacent tail ih =>
      apply List.pairwise_cons.mpr
      refine ⟨?_,ih⟩
      intro b mem
      rcases List.mem_cons.mp mem with eq | later
      · subst b; exact decreasing adjacent
      · exact lex_trans ((List.pairwise_cons.mp ih).1 b later) (decreasing adjacent)
  exact pairwise.imp (fun {a b} h (eq : a = b) => lex_irrefl _ (eq ▸ h))

end SharingTreeExpansion

/-- A contraction-tree context has sharing primitives and explicitly typed
sharing holes; each hole has finitely many same-sort inputs and one output. -/
structure SharingTreeContext (s : ShareSort) (m d : Nat) where
  net : Hypernet d (List.replicate m s.wire) [s.wire]
  labels : ∀ e, net.edgeLabel e = primitiveLabel d (.weakening s) ∨
    net.edgeLabel e = primitiveLabel d (.contraction s) ∨
    ∃ h n, net.edgeLabel e = primitiveLabel d (.hole h) ∧
      h.input = List.replicate n s.wire ∧ h.output = [s.wire]
  acyclic : ∀ {es}, net.Path es → es.Nodup

namespace SharingTreeContext
variable {s : ShareSort} {m d : Nat} (C : SharingTreeContext s m d)

/-- Every original sharing-context edge has one target, including holes. -/
theorem target_single (e : C.net.Edge) : (C.net.target e).length = 1 := by
  rw [C.net.target_length]
  rcases C.labels e with h | h | ⟨h,n,label,input,output⟩
  · rw [h,primitive_output]; rfl
  · rw [h,primitive_output]; rfl
  · rw [label,primitive_output]; exact congrArg List.length output

/-- Any simultaneous family of actual contraction trees supplies an acyclic
expanded graph, independently of the presentation of each tree. -/
theorem expansion_acyclic
    (H : (e : C.net.Edge) → Hypernet d ((alphabet d).signature.input (C.net.edgeLabel e))
      ((alphabet d).signature.output (C.net.edgeLabel e)))
    (labels : ∀ e f, (H e).edgeLabel f = primitiveLabel d (.weakening s) ∨
      (H e).edgeLabel f = primitiveLabel d (.contraction s))
    (acyclic : ∀ e {es}, (H e).Path es → es.Nodup) :
    ∀ {es}, (C.net.expand H).Path es → es.Nodup := by
  apply SharingTreeExpansion.acyclic_expand C.net H C.acyclic C.target_single acyclic
  intro e f
  rw [(H e).target_length]
  rcases labels e f with h | h <;> rw [h,primitive_output] <;> rfl

end SharingTreeContext
end Hypernets.Copying

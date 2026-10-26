import Hypernets.Copying.ArithmeticLocalReduction

/-! Every actual contextual arithmetic rewrite determines its complete successor. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Arithmetic
open Graph MatchEmbedding Combined

inductive Request where
  | neg (operand : Nat)
  | binary (operation : BinaryCode) (left right : Nat)

def Request.choice : Request → Combined.Choice
  | .neg n => .neg n
  | .binary o m n => .binary o m n

def Request.result : Request → Nat
  | .neg n => Arithmetic.neg n
  | .binary o m n => o.eval m n

theorem Request.choice_injective {r s : Request} (eq : r.choice = s.choice) : r = s := by
  cases r <;> cases s <;> cases eq <;> rfl

/-- The evidence is derived from the actual rewrite and includes the resumed token. -/
structure Certificate {d I O} (G H : Hypernet d I O) (v : G.Vertex) (w : H.Vertex) (r : Request) where
  head : G.Edge
  head_at : HeadAt G v head r.choice.head
  closed : InternalTargets G head
  reduction : Reduction G H head r.result
  token : Port.map reduction.vertices w = v

theorem internalTargets_rename {d I O} {G H : Hypernet d I O} (f : DeepIso G H) {e}
    (closed : InternalTargets G e) : InternalTargets H (f.edges.toFun e) := by
  intro v hv
  rw [← f.target] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  obtain ⟨x,rfl⟩ := closed w hw
  exact ⟨f.vertices.toFun x,rfl⟩

def Certificate.rename {d I O} {G H G' H' : Hypernet d I O} {v w r}
    (a : Certificate G H v w r) (f : DeepIso G G') (g : DeepIso H H') :
    Certificate G' H' (Port.map f.vertices.toFun v) (Port.map g.vertices.toFun w) r where
  head := f.edges.toFun a.head
  head_at := (MatchEmbedding.ofDeepIso f).head a.head_at
  closed := internalTargets_rename f a.closed
  reduction := (a.reduction.sourceRename f).targetRename g.symm
  token := by
    rw [Reduction.targetRename_port]
    have inv := (Port.bijection g.vertices).left_inv w
    change Port.map g.vertices.invFun (Port.map g.vertices.toFun w) = w at inv
    change Port.map (a.reduction.sourceRename f).vertices (Port.map g.vertices.invFun (Port.map g.vertices.toFun w)) = _
    rw [inv,Reduction.sourceRename_port,a.token]

def Certificate.plug {d I O} (C : Hypernet d I O) (hole : C.Edge)
    {G H : Hypernet d ((alphabet d).signature.input (C.edgeLabel hole)) ((alphabet d).signature.output (C.edgeLabel hole))}
    {v w r} (a : Certificate G H v w r) :
    Certificate (C.plug hole G) (C.plug hole H) (Net.Replacement.insert C hole G v)
      (Net.Replacement.insert C hole H w) r where
  head := .inr a.head
  head_at := (MatchEmbedding.plug C hole G).head a.head_at
  closed := Reduction.plug_closed C hole a.closed
  reduction := a.reduction.plug C hole a.closed
  token := (Reduction.plug_port C hole a.reduction w).trans (congrArg (Net.Replacement.insert C hole G) a.token)

noncomputable def Certificate.expand {d I O} (C : Hypernet d I O)
    (F K : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (hole : C.Edge) (others : ∀ e, e ≠ hole → F e = K e) {v w r}
    (a : Certificate (F hole) (K hole) v w r) :
    Certificate (C.expand F) (C.expand K) (Net.Expansion.insert C F hole v)
      (Net.Expansion.insert C K hole w) r where
  head := ⟨hole,a.head⟩
  head_at := (MatchEmbedding.expand C F hole).head a.head_at
  closed := Reduction.expansion_closed C F hole a.closed
  reduction := a.reduction.expand C F K hole others a.closed
  token := by
    change Port.map (Reduction.expansionVertices C F K hole others a.reduction) (Net.Expansion.insert C K hole w) = _
    rw [Reduction.expansion_port,Reduction.fiber_vertices_same,a.token]

/-- The original unary rule has the expected source-relative certificate. -/
def unary_certificate (d n : Nat) :
    Certificate (unaryBefore d n) (unaryAfter d n) (.input 0) (.input 0) (.neg n) where
  head := unaryHead d n
  head_at := unary_head d n
  closed := unary_internal_targets d n
  reduction := unary_reduction d n
  token := rfl

def binary_certificate (o : BinaryCode) (d m n : Nat) :
    Certificate (binaryBefore o d m n) (binaryAfter o d m n) (.input 0) (.input 0) (.binary o m n) where
  head := binaryHead o d m n
  head_at := binary_head o d m n
  closed := binary_internal_targets o d m n
  reduction := binary_reduction o d m n
  token := rfl
end Hypernets.Copying.Arithmetic

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding Arithmetic

/-- The unique actual rule choice reflects into any selected rewritten component. -/
theorem rewrite_recognition_reflect {d r I O J K} {G H : Hypernet d I O} {N : Hypernet r J K}
    {v w c} (step : Rewrite G v H w) (f : MatchEmbedding G N) (recognized : Recognizes N (f.ports v) c) :
    Recognizes G v c := by
  obtain ⟨b,hb⟩ := rewrite_recognizes step
  exact recognizes_unique (recognizes_map f hb) recognized ▸ hb

theorem local_arithmetic_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Local G v H w) (r : Request) (recognized : Recognizes G v r.choice) :
    Nonempty (Certificate G H v w r) := by
  have witness := recognized
  obtain ⟨e,head,_⟩ := witness
  cases step with
  | unaryArithmetic d n =>
    have eq := Request.choice_injective (s := .neg n)
      (recognizes_unique recognized ⟨unaryHead d n,unary_head d n,unary_operand d n⟩)
    subst r
    exact ⟨unary_certificate d n⟩
  | binaryArithmetic o d m n =>
    have eq := Request.choice_injective (s := .binary o m n)
      (recognizes_unique recognized ⟨binaryHead o d m n,binary_head o d m n,
        binary_left_operand o d m n,binary_right_operand o d m n⟩)
    subst r
    exact ⟨binary_certificate o d m n⟩
  | allocate G stable =>
    have bad := (head_unique head (Allocation.head_at G)).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> try cases bad
  | read T d =>
    have bad := (head_unique head (Dereference.localMatch T d).head).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> try cases bad
  | assign T G stable =>
    have bad := (head_unique head (Assignment.localMatch T G).head).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> try cases bad
    all_goals cases ‹BinaryCode› <;> cases bad
  | same T d =>
    have bad := (head_unique head (AtomEquality.Same.head_at T d)).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> try cases bad
    all_goals cases ‹BinaryCode› <;> cases bad
  | different T U d =>
    have bad := (head_unique head (AtomEquality.Different.head_at T U d)).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> try cases bad
    all_goals cases ‹BinaryCode› <;> cases bad
  | beta B G stable =>
    have bad := (head_unique head (show HeadAt (Application.before B G) _ ⟨false,(0 : Fin 1)⟩
      (.operation .app) from ⟨rfl,List.mem_cons_self⟩)).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> cases bad
  | copy T G copyable =>
    obtain ⟨h,chosen⟩ := CopyRule.before_active_head T G ⟨0,by simp⟩
    have bad := (head_unique head chosen).2
    cases r <;> simp only [Request.choice,Choice.head] at bad <;> cases bad

/-- Complete arithmetic certificates follow every actual contextual rewrite constructor. -/
theorem rewrite_arithmetic_certificate {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) (r : Request) (recognized : Recognizes G v r.choice) :
    Nonempty (Certificate G H v w r) := by
  induction step with
  | «local» step => exact local_arithmetic_certificate step r recognized
  | rename f g step ih =>
    obtain ⟨a⟩ := ih (rewrite_recognition_reflect step (MatchEmbedding.ofDeepIso f) recognized)
    exact ⟨a.rename f g⟩
  | plug C hole step ih =>
    obtain ⟨a⟩ := ih (rewrite_recognition_reflect step (MatchEmbedding.plug C hole _) recognized)
    exact ⟨a.plug C hole⟩
  | expand C F K hole others step ih =>
    obtain ⟨a⟩ := ih (rewrite_recognition_reflect step (MatchEmbedding.expand C F hole) recognized)
    exact ⟨a.expand C F K hole others⟩

/-- Independently chosen arithmetic matches give recursively isomorphic complete successors. -/
theorem arithmetic_rewrite_deterministic {d I O} {G H K : Hypernet d I O} {v w u}
    (r : Request) (recognized : Recognizes G v r.choice)
    (first : Rewrite G v H w) (second : Rewrite G v K u) :
    Nonempty (StateIso ⟨H,(.search,w)⟩ ⟨K,(.search,u)⟩) := by
  obtain ⟨a⟩ := rewrite_arithmetic_certificate first r recognized
  obtain ⟨b⟩ := rewrite_arithmetic_certificate second r recognized
  have same := (head_unique a.head_at b.head_at).1
  cases a with
  | mk ah ahead ac ar tokenA =>
    cases b with
    | mk bh bhead bc br bt =>
      dsimp only at same
      subst bh
      exact ⟨ar.stateIso br (tokenA.trans bt.symm)⟩

theorem arithmetic_step_deterministic {d I O} {G : Hypernet d I O} {v} {s t : State d I O}
    (r : Request) (recognized : Recognizes G v r.choice)
    (first : Step ⟨G,(.rewrite,v)⟩ s) (second : Step ⟨G,(.rewrite,v)⟩ t) :
    Nonempty (StateIso s t) := by
  cases first with
  | search _ h => exact False.elim (Search.no_rewrite h)
  | rewrite first =>
    cases second with
    | search _ h => exact False.elim (Search.no_rewrite h)
    | rewrite second => exact arithmetic_rewrite_deterministic r recognized first second

theorem arithmetic_cost_spectrum {d I O} {G : Hypernet d I O} {v} {t : State d I O}
    (r : Request) (recognized : Recognizes G v r.choice) (step : Step ⟨G,(.rewrite,v)⟩ t) (n : Nat) :
    TerminatesIn n ⟨G,(.rewrite,v)⟩ ↔ ∃ m, n = m+1 ∧ TerminatesIn m t :=
  coherent_step_cost_iff step (fun _ h => arithmetic_step_deterministic r recognized h step) n

theorem arithmetic_unbounded_deterministic {d} {G : Hypernet d [.term] []} {v} {s t : UnboundedState}
    (r : Request) (recognized : Recognizes G v r.choice)
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    Represents s t := by
  cases first with
  | lift first =>
    cases second with
    | lift second =>
      obtain ⟨iso⟩ := arithmetic_step_deterministic r recognized first second
      exact .lift iso

theorem arithmetic_unbounded_equiv (Q : CostOrder) {d} {G : Hypernet d [.term] []} {v} {s t : UnboundedState}
    (r : Request) (recognized : Recognizes G v r.choice)
    (first : UnboundedStep ⟨d,G,(.rewrite,v)⟩ s) (second : UnboundedStep ⟨d,G,(.rewrite,v)⟩ t) :
    unboundedMachine.Equiv Q s t :=
  represents_equiv Q (arithmetic_unbounded_deterministic r recognized first second)
end Hypernets.Copying.Combined

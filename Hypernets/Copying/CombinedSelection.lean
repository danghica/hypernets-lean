import Hypernets.Copying.ArithmeticMatching

/-! Unique rule and operand selection for every contextual combined rewrite.
Selection is a derived invariant; the operational relation itself is unchanged. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Combined
open Graph MatchEmbedding

/-- Observable matching data, before any comparison of rewritten graph representations. -/
inductive Choice where
  | allocate | read | assign | beta
  | compare (result : Bool)
  | copy (payload : Primitive)
  | neg (operand : Nat)
  | binary (operation : Arithmetic.BinaryCode) (left right : Nat)

def Choice.head : Choice → Primitive
  | .allocate => .operation (.unary .ref)
  | .read => .operation (.unary .deref)
  | .assign => .operation (.binary .assign)
  | .beta => .operation .app
  | .compare _ => .operation (.binary .atomEq)
  | .copy _ => .contraction .term
  | .neg _ => .operation (.unary .neg)
  | .binary o _ _ => .operation (.binary o.symbol)

/-- Recognition only reads the source graph: operation, ordered operands, sharing and stores. -/
def Recognizes {d I O} (G : Hypernet d I O) (v : G.Vertex) (choice : Choice) : Prop :=
  ∃ e, HeadAt G v e choice.head ∧ match choice with
    | .compare b => AtomEquality.Decision G v b
    | .copy p => ∃ a n, CopyTrace.Resolves G v a p n
    | .neg n => Arithmetic.NumberArgument G e 0 n
    | .binary _ m n => Arithmetic.NumberArgument G e 0 m ∧ Arithmetic.NumberArgument G e 1 n
    | _ => True

/-- Attachment, simultaneous expansion, recursive renaming and padding preserve recognition. -/
theorem recognizes_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v c} (h : Recognizes G v c) : Recognizes H (f.ports v) c := by
  obtain ⟨e,head,data⟩ := h
  refine ⟨f.edges e,f.head head,?_⟩
  cases c with
  | compare b => exact AtomEquality.decision_map f data
  | copy p => obtain ⟨a,n,trace⟩ := data; exact ⟨f.edges a,n,CopyTrace.resolves_map f trace⟩
  | neg n => exact Arithmetic.numberArgument_map f data
  | binary o m n => exact ⟨Arithmetic.numberArgument_map f data.1,Arithmetic.numberArgument_map f data.2⟩
  | _ => trivial

/-- Every source token has at most one rule choice, including numeric operands and atom result. -/
theorem recognizes_unique {d I O} {G : Hypernet d I O} {v a b}
    (ha : Recognizes G v a) (hb : Recognizes G v b) : a = b := by
  obtain ⟨e,head,data⟩ := ha
  obtain ⟨f,head',data'⟩ := hb
  obtain ⟨edge,label⟩ := head_unique head head'
  subst f
  cases a <;> cases b <;> simp only [Choice.head] at label <;> try cases label
  all_goals first
    | rfl
    | exact congrArg Choice.compare (AtomEquality.decision_unique data data')
    | exact congrArg Choice.neg (Arithmetic.numberArgument_unique data data')
    | (obtain ⟨x,n,hx⟩ := data
       obtain ⟨y,m,hy⟩ := data'
       exact congrArg Choice.copy (CopyTrace.resolves_unique hx hy).2.1)
    | (rename_i o m n p a b
       have codes := Arithmetic.BinaryCode.symbol_injective
         (Operation.binary.inj (Primitive.operation.inj label))
       have left := Arithmetic.numberArgument_unique data.1 data'.1
       have right := Arithmetic.numberArgument_unique data.2 data'.2
       cases codes; cases left; cases right; rfl)
    | (cases ‹Arithmetic.BinaryCode› <;> simp_all [Arithmetic.BinaryCode.symbol])

/-- Every primitive redex has a recognition witness, with its original stability/copyability premises. -/
theorem local_recognizes {d I O} {G H : Hypernet d I O} {v w} (step : Local G v H w) :
    ∃ c, Recognizes G v c := by
  cases step with
  | @allocate d O G stable =>
    refine ⟨.allocate,Serial.leftEdge _ _ (by cases d <;> exact (0 : Fin 1)),?_,trivial⟩
    cases d <;> exact ⟨rfl,List.mem_cons_self⟩
  | read T d => exact ⟨.read,⟨.reader,(0 : Fin 1)⟩,⟨rfl,List.mem_cons_self⟩,trivial⟩
  | @assign d h O T G stable =>
    cases d <;> exact ⟨.assign,⟨.assign,(0 : Fin 1)⟩,⟨rfl,List.mem_cons_self⟩,trivial⟩
  | same T d => exact ⟨.compare true,⟨.compare,(0 : Fin 1)⟩,⟨rfl,List.mem_cons_self⟩,AtomEquality.Same.before_decision T d⟩
  | different T U d => exact ⟨.compare false,⟨.compare,(0 : Fin 1)⟩,⟨rfl,List.mem_cons_self⟩,AtomEquality.Different.before_decision T U d⟩
  | beta B G stable => exact ⟨.beta,⟨false,(0 : Fin 1)⟩,⟨rfl,List.mem_cons_self⟩,trivial⟩
  | copy T G copyable =>
    obtain ⟨e,head⟩ := CopyRule.before_active_head T G ⟨0,by simp⟩
    obtain ⟨a,p,n,_,trace⟩ := CopyRule.before_resolves T G copyable ⟨0,by simp⟩
    exact ⟨.copy p,e,head,_,n+1,trace⟩
  | unaryArithmetic d n => exact ⟨.neg n,Arithmetic.unaryHead d n,Arithmetic.unary_head d n,Arithmetic.unary_operand d n⟩
  | binaryArithmetic o d m n => exact ⟨.binary o m n,Arithmetic.binaryHead o d m n,
      Arithmetic.binary_head o d m n,Arithmetic.binary_left_operand o d m n,Arithmetic.binary_right_operand o d m n⟩

/-- Recognition holds for all actual rewrites, however their host decomposition was chosen. -/
theorem rewrite_recognizes {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    ∃ c, Recognizes G v c := by
  induction step with
  | «local» step => exact local_recognizes step
  | rename f g step ih => obtain ⟨c,h⟩ := ih; exact ⟨c,recognizes_map (MatchEmbedding.ofDeepIso f) h⟩
  | plug C e step ih => obtain ⟨c,h⟩ := ih; exact ⟨c,recognizes_map (MatchEmbedding.plug C e _) h⟩
  | expand C F K e others step ih => obtain ⟨c,h⟩ := ih; exact ⟨c,recognizes_map (MatchEmbedding.expand C F e) h⟩

/-- A rewritten source has exactly one recognized rule choice. This is selection determinism,
not yet isomorphism of the successor graphs. -/
theorem rewrite_unique_choice {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    ∃ c, Recognizes G v c ∧ ∀ b, Recognizes G v b → b = c := by
  obtain ⟨c,h⟩ := rewrite_recognizes step
  exact ⟨c,h,fun _ h' => recognizes_unique h' h⟩

/-- Every recognized head is active or a term contraction. -/
theorem choice_head_active (c : Choice) :
    c.head = .contraction .term ∨ ∃ o, c.head = .operation o ∧ o.kind = .active := by
  cases c <;> simp [Choice.head,Operation.kind]

/-- Stable graphs cannot support any contextual rewrite, at any vertex. -/
theorem stable_no_rewrite {d O} {G : Hypernet d [.term] O} (stable : Stable G) {H v w} : ¬ Rewrite G v H w := by
  intro step
  obtain ⟨c,e,head,_⟩ := rewrite_recognizes step
  obtain ⟨p,label,hp⟩ := stable.labels e
  have same := primitiveLabel_injective d (head.1.symm.trans label)
  rcases choice_head_active c with contr | ⟨o,op,active⟩
  · rw [contr] at same; subst p; exact hp
  · rw [op] at same; subst p
    change o.kind = .passive at hp
    rw [active] at hp; cases hp

/-- A contextual rewrite is never based at an external output. -/
theorem rewrite_not_output {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) : ¬ v.IsOutput := by
  obtain ⟨c,e,head,_⟩ := rewrite_recognizes step
  exact G.source_not_output head.2
/-- A stable payload remains non-rewritable at its input even inside an arbitrary host. -/
theorem stable_occurrence_no_rewrite {r d O I J} {A : Hypernet r [.term] O} {G H : Hypernet d I J}
    (stable : Stable A) (f : MatchEmbedding A G) {w} : ¬ Rewrite G (f.ports (.input 0)) H w := by
  intro step
  obtain ⟨e,src⟩ := (A.source_coverage (.input 0)).mpr (by simp [Port.IsOutput])
  obtain ⟨p,label,passive⟩ := stable.labels e
  have head := f.head (show HeadAt A (.input 0) e p from ⟨label,src⟩)
  obtain ⟨c,a,chosen,_⟩ := rewrite_recognizes step
  have eq := (head_unique chosen head).2
  rcases choice_head_active c with contr | ⟨o,op,active⟩
  · rw [contr] at eq; subst p; exact passive
  · rw [op] at eq; subst p
    change o.kind = .passive at passive
    rw [active] at passive; cases passive

/-- Full search transports preserve and reflect source recognition. -/
theorem recognizes_transport_iff {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : Search.Transport G H) (v : G.Vertex) (c : Choice) :
    Recognizes H (f.ports.toFun v) c ↔ Recognizes G v c := by
  constructor
  · intro h
    have back := recognizes_map (MatchEmbedding.ofTransport f.symm) h
    simpa only [MatchEmbedding.ofTransport,Search.Transport.symm,Bijection.symm,f.ports.left_inv] using back
  · exact recognizes_map (MatchEmbedding.ofTransport f)

/-- The selected rule and its operands are independent of unused box allowance. -/
theorem recognizes_pad_iff {d I O} (G : Hypernet d I O) (layers : Nat) (v : G.Vertex) (c : Choice) :
    Recognizes (Translation.pad d layers G) ((Search.pad G layers).ports.toFun v) c ↔ Recognizes G v c :=
  recognizes_transport_iff (Search.pad G layers) v c

end Hypernets.Copying.Combined

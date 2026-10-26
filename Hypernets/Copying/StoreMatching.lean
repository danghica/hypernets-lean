import Hypernets.Copying.CopyMatching

/-! Reference-identity decisions are independent of matched atom trees and contexts. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph MatchEmbedding
namespace StoreTrace

theorem hop_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {a b} (h : Hop G a b) : Hop H (f.edges a) (f.edges b) := by
  refine ⟨?_,f.adjacent h.2⟩
  rcases h.1 with h | h | h
  · exact .inl (f.primitive _ _ h)
  · exact .inr (.inl (f.primitive _ _ h))
  · exact .inr (.inr (f.primitive _ _ h))

theorem resolves_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {a b n} (h : Resolves G a b n) : Resolves H (f.edges a) (f.edges b) n :=
  ⟨h.1.map f.edges (hop_map f),f.primitive _ _ h.2⟩

/-- Resolve a specified operation argument to its actual store occurrence. -/
def Operand {d I O} (G : Hypernet d I O) (v : G.Vertex) (o : Operation) (i : Nat) (s : G.Edge) (n : Nat) : Prop :=
  ∃ e a, HeadAt G v e (.operation o) ∧ Argument G e i a ∧ Resolves G a s n

/-- Independent decompositions of the same argument choose the same store and cost. -/
theorem operand_unique {d I O} {G : Hypernet d I O} {v o i a b n m}
    (ha : Operand G v o i a n) (hb : Operand G v o i b m) : a = b ∧ n = m := by
  obtain ⟨e,x,head,arg,trace⟩ := ha
  obtain ⟨f,y,head',arg',trace'⟩ := hb
  have ef := (head_unique head head').1
  subst f
  have xy := argument_unique arg arg'
  subst y
  exact resolves_unique trace trace'

theorem operand_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v o i s n} (h : Operand G v o i s n) :
    Operand H (f.ports v) o i (f.edges s) n := by
  obtain ⟨e,a,head,arg,trace⟩ := h
  exact ⟨f.edges e,f.edges a,f.head head,f.argument arg,resolves_map f trace⟩
end StoreTrace

namespace Dereference
/-- The local read's selected argument resolves to its retained store occurrence. -/
theorem before_operand {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    ∃ n, StoreTrace.Operand (before T d) (inputPort h 0) (.unary .deref) 0 (beforeStore T d) n := by
  obtain ⟨n,trace,_⟩ := resolves_both T d
  exact ⟨n,⟨.reader,(0 : Fin 1)⟩,beforeInstance T d,⟨rfl,List.mem_cons_self⟩,
    ⟨argument T d,rfl,List.mem_cons_self⟩,trace⟩

/-- Independently embedded reads at one token cannot read different cells. -/
theorem match_store_unique {d r s I O h k} {G : Hypernet d I O}
    (T : ContractionTree .atom (h+1)) (U : ContractionTree .atom (k+1))
    (f : MatchEmbedding (before T r) G) (g : MatchEmbedding (before U s) G)
    (same : f.ports (inputPort h 0) = g.ports (inputPort k 0)) :
    f.edges (beforeStore T r) = g.edges (beforeStore U s) := by
  obtain ⟨n,ha⟩ := before_operand T r
  obtain ⟨m,hb⟩ := before_operand U s
  have a := StoreTrace.operand_map f ha
  rw [same] at a
  exact (StoreTrace.operand_unique a (StoreTrace.operand_map g hb)).1
end Dereference

namespace Assignment
/-- The local assignment identifies its destination through argument zero. -/
theorem before_operand {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    ∃ n, StoreTrace.Operand (before T G) (inputPort h O 0) (.binary .assign) 0 (beforeStore T G) n := by
  obtain ⟨n,trace,_⟩ := resolves_both T G
  cases d <;> exact ⟨n,⟨.assign,(0 : Fin 1)⟩,beforeInstance T G,⟨rfl,List.mem_cons_self⟩,
    ⟨instanceArgument T G,rfl,List.mem_cons_self⟩,trace⟩

/-- Independently embedded writes at one token cannot choose different destinations. -/
theorem match_store_unique {d r s I O h k A B} {G : Hypernet d I O}
    (T : ContractionTree .atom (h+1)) (U : ContractionTree .atom (k+1))
    (V : Hypernet r [.term] A) (W : Hypernet s [.term] B)
    (f : MatchEmbedding (before T V) G) (g : MatchEmbedding (before U W) G)
    (same : f.ports (inputPort h A 0) = g.ports (inputPort k B 0)) :
    f.edges (beforeStore T V) = g.edges (beforeStore U W) := by
  obtain ⟨n,ha⟩ := before_operand T V
  obtain ⟨m,hb⟩ := before_operand U W
  have a := StoreTrace.operand_map f ha
  rw [same] at a
  exact (StoreTrace.operand_unique a (StoreTrace.operand_map g hb)).1
end Assignment

namespace AtomEquality
/-- The Boolean result is determined by equality of resolved store edges, not their contents. -/
def Decision {d I O} (G : Hypernet d I O) (v : G.Vertex) (b : Bool) : Prop :=
  ∃ s t n m, StoreTrace.Operand G v (.binary .atomEq) 0 s n ∧
    StoreTrace.Operand G v (.binary .atomEq) 1 t m ∧ (s = t ↔ b = true)

/-- No two matches at the same comparison request can disagree on the result. -/
theorem decision_unique {d I O} {G : Hypernet d I O} {v a b}
    (ha : Decision G v a) (hb : Decision G v b) : a = b := by
  obtain ⟨s,t,n,m,ls,rt,eq⟩ := ha
  obtain ⟨s',t',n',m',ls',rt',eq'⟩ := hb
  have ss := (StoreTrace.operand_unique ls ls').1
  have tt := (StoreTrace.operand_unique rt rt').1
  subst s'; subst t'
  have iff := eq.symm.trans eq'
  cases a <;> cases b <;> simp_all

/-- Edge-injective occurrences preserve both equality and disequality of stores. -/
theorem decision_map {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : MatchEmbedding G H) {v b} (h : Decision G v b) : Decision H (f.ports v) b := by
  obtain ⟨s,t,n,m,ls,rt,eq⟩ := h
  refine ⟨f.edges s,f.edges t,n,m,StoreTrace.operand_map f ls,StoreTrace.operand_map f rt,?_⟩
  exact (⟨fun h => f.edge_injective h,congrArg f.edges⟩ : f.edges s = f.edges t ↔ s = t).trans eq

namespace Same
/-- The one-store local rule satisfies the intrinsic identity decision. -/
theorem before_decision {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    Decision (before T d) (inputPort h 0) true := by
  obtain ⟨n,left,_⟩ := resolves_left T d
  obtain ⟨m,right,_⟩ := resolves_right T d
  refine ⟨beforeStore T d,beforeStore T d,n,m,?_,?_,by simp⟩
  · refine ⟨⟨.compare,(0 : Fin 1)⟩,beforeLeft T d,⟨rfl,List.mem_cons_self⟩,?_,left⟩
    exact ⟨leftArgument T d,rfl,List.mem_cons_self⟩
  · refine ⟨⟨.compare,(0 : Fin 1)⟩,beforeRight T d,⟨rfl,List.mem_cons_self⟩,?_,right⟩
    exact ⟨rightArgument T d,rfl,List.mem_cons_self⟩
end Same
namespace Different
/-- The two-store local rule retains the distinct identities of both stores. -/
theorem before_decision {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    Decision (before T U d) (inputPort n m 0) false := by
  obtain ⟨a,left,_⟩ := resolves_left T U d
  obtain ⟨b,right,_⟩ := resolves_right T U d
  refine ⟨beforeStore T U d,beforeStoreRight T U d,a,b,?_,?_,?_⟩
  · refine ⟨⟨.compare,(0 : Fin 1)⟩,beforeLeft T U d,⟨rfl,List.mem_cons_self⟩,?_,left⟩
    exact ⟨leftArgument T U d,rfl,List.mem_cons_self⟩
  · refine ⟨⟨.compare,(0 : Fin 1)⟩,beforeRight T U d,⟨rfl,List.mem_cons_self⟩,?_,right⟩
    exact ⟨rightArgument T U d,rfl,List.mem_cons_self⟩
  · constructor
    · intro eq; cases congrArg Sigma.fst eq
    · intro eq; cases eq
end Different

/-- Independently embedded one-store and two-store rules cannot match the same token. -/
theorem same_different_disjoint {d r s I O h n m} {G : Hypernet d I O}
    (T : ContractionTree .atom (h+2)) (U : ContractionTree .atom (n+1)) (V : ContractionTree .atom (m+1))
    (f : MatchEmbedding (Same.before T r) G) (g : MatchEmbedding (Different.before U V s) G) :
    f.ports (Same.inputPort h 0) ≠ g.ports (Different.inputPort n m 0) := by
  intro eq
  have a := decision_map f (Same.before_decision T r)
  have b := decision_map g (Different.before_decision U V s)
  rw [eq] at a
  have bad := decision_unique a b
  cases bad
end AtomEquality
end Hypernets.Copying

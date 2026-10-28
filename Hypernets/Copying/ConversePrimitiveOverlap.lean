import Hypernets.Copying.ConverseHeadOrigin

/-! Exhaustive converse footprints for arithmetic and allocation, from the
original left endpoint's rooted search history. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Search.Expansion

/-- A local rule consisting of its active head and its direct argument edges
has no shallow right operational overlap. -/
theorem simple_avoids {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    {J K} {A : Hypernet d J K} (f : MatchEmbedding A (C.expand R))
    {a head o} (selected : MatchEmbedding.HeadAt A a head (.operation o))
    (active : o.kind = .active) (attached : f.ports a = Net.Expansion.host C R v)
    (cases_ : ∀ e, e = head ∨ A.Adjacent head e) :
    RetainedFootprint.AvoidsShallow C f := by
  have chosen : MatchEmbedding.HeadAt (C.expand R) (Net.Expansion.host C R v)
      (f.edges head) (.operation o) := by
    rw [← attached]; exact f.head selected
  intro e h hole
  rcases cases_ e with rfl | adj
  · exact away ⟨_,h,hole,source_owner C R chosen.2⟩
  · exact adjacent_source_not_hole C cert away rooted chosen active (f.adjacent adj) h hole

/-- Every outer allocation edge is its active head or an evaluated operand. -/
theorem allocation_edges {d O} (G : Hypernet d [.term] O) (stable : Stable G)
    (e : (Allocation.before G).Edge) :
    e = Allocation.head G ∨ (Allocation.before G).Adjacent (Allocation.head G) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left; cases d
    all_goals cases DiscardResult.fin_one e; rfl
  | true =>
    right; cases d
    all_goals exact ⟨.internal (.inl (0 : Fin 1)),List.mem_cons_self,
      List.mem_map_of_mem (Stable.input_source stable.labels e)⟩

/-- Allocation is classified without changing its stable operand or interface. -/
theorem allocation_avoids {kind d I O J} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (G : Hypernet d [.term] J) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert away rooted f.matchEmbedding (Allocation.head_at G) rfl attached
    (allocation_edges G stable)

/-- Unary arithmetic has only its head and one evaluated constant. -/
theorem unary_edges (d n : Nat) (e : (Arithmetic.unaryBefore d n).Edge) :
    e = Arithmetic.unaryHead d n ∨
      (Arithmetic.unaryBefore d n).Adjacent (Arithmetic.unaryHead d n) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left; cases d
    all_goals cases DiscardResult.fin_one e; rfl
  | true =>
    right; cases d
    all_goals exact ⟨.internal (.inl (0 : Fin 1)),List.mem_cons_self,List.mem_cons_self⟩

/-- Binary arithmetic has only its head and the two ordered constants. -/
theorem binary_edges (o : Arithmetic.BinaryCode) (d m n : Nat)
    (e : (Arithmetic.binaryBefore o d m n).Edge) :
    e = Arithmetic.binaryHead o d m n ∨
      (Arithmetic.binaryBefore o d m n).Adjacent (Arithmetic.binaryHead o d m n) e := by
  obtain ⟨part,e⟩ := e
  cases part with
  | false =>
    left; cases d
    all_goals cases DiscardResult.fin_one e; rfl
  | true =>
    right; cases d
    all_goals obtain ⟨side,e⟩ := e; cases side
    all_goals first
      | exact ⟨.internal (.inl (0 : Fin 2)),List.mem_cons_self,List.mem_cons_self⟩
      | exact ⟨.internal (.inl (1 : Fin 2)),List.mem_cons_of_mem _ List.mem_cons_self,List.mem_cons_self⟩

/-- Exact unary footprints avoid all original shallow right holes. -/
theorem unary_avoids {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (n : Nat) (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert away rooted f.matchEmbedding (Arithmetic.unary_head d n) rfl attached
    (unary_edges d n)

/-- Exact binary footprints avoid all original shallow right holes. -/
theorem binary_avoids {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (o : Arithmetic.BinaryCode) (m n : Nat)
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert away rooted f.matchEmbedding (Arithmetic.binary_head o d m n)
    (by cases o <;> rfl) attached (binary_edges o d m n)

end Hypernets.Copying.OperationalTemplates.ConverseOverlap

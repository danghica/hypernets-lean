import Hypernets.Copying.CopyingTemplateConverseHead
import Hypernets.Copying.ConversePrimitiveOverlap

/-! Exhaustive converse footprints for arithmetic and allocation, from the
original left endpoint's rooted search history. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingTemplate.ConverseOverlap
open Graph Search.Expansion

/-- A local rule consisting of its active head and its direct argument edges
has no shallow right copying overlap. -/
theorem simple_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {input v} (away : ¬ Entering C (.rewrite,v))
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
  · exact adjacent_source_not_hole C cert closed away rooted chosen active (f.adjacent adj) h hole

/-- Allocation is classified without changing its stable operand or interface. -/
theorem allocation_avoids {d I O J} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (G : Hypernet d [.term] J) (stable : Stable G)
    (f : Opening.Occurrence (Allocation.before G) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert closed away rooted f.matchEmbedding (Allocation.head_at G) rfl attached
    (OperationalTemplates.ConverseOverlap.allocation_edges G stable)

/-- Exact unary footprints avoid all original shallow right holes. -/
theorem unary_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (n : Nat) (f : Opening.Occurrence (Arithmetic.unaryBefore d n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert closed away rooted f.matchEmbedding (Arithmetic.unary_head d n) rfl attached
    (OperationalTemplates.ConverseOverlap.unary_edges d n)

/-- Exact binary footprints avoid all original shallow right holes. -/
theorem binary_avoids {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge template C L R e)
    (closed : HoleFree (C.expand L)) {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    (o : Arithmetic.BinaryCode) (m n : Nat)
    (f : Opening.Occurrence (Arithmetic.binaryBefore o d m n) (C.expand R))
    (attached : f.ports (.input 0) = Net.Expansion.host C R v) :
    RetainedFootprint.AvoidsShallow C f.matchEmbedding :=
  simple_avoids C cert closed away rooted f.matchEmbedding (Arithmetic.binary_head o d m n)
    (by cases o <;> rfl) attached (OperationalTemplates.ConverseOverlap.binary_edges o d m n)

end Hypernets.Copying.CopyingTemplate.ConverseOverlap

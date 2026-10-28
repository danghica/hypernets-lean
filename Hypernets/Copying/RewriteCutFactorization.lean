import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.CopyCoherence

/-! Every original contextual rewrite factors through its constructed finite
cut. The supplied successor, including its resumed token, is recursively
isomorphic to the cut replacement; this is not merely existence of another
rewrite from the same source. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

namespace Opening.Occurrence
variable {d I O J K} {A B : Hypernet d J K} {G H : Hypernet d I O}
    (f : Occurrence A G)

/-- The actual successor agrees with replacement of this complete matched
occurrence. The original local rule's premises are used unchanged. -/
theorem rewrite_successor {a : A.Vertex} {b : B.Vertex} {w : H.Vertex}
    (localStep : Combined.Rewrite A a B b)
    (actual : Combined.Rewrite G (f.ports a) H w) :
    Nonempty (Combined.StateIso ⟨H,(.search,w)⟩
      ⟨CompleteMatchCut.replaceWith f.matchEmbedding f.label B,
        (.search,CompleteMatchCut.replacePort f.matchEmbedding f.label B b)⟩) :=
  Combined.rewrite_deterministic actual (f.rewrite localStep)

end Opening.Occurrence

namespace Combined

/-- A checked finite factorization of an actual rewrite. The local source is
fully labelled; the target is the explicit finite complement with only that
source replaced, up to recursive representation of the supplied successor. -/
structure CutFactorization {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  input : List Wire
  output : List Wire
  before : Hypernet d input output
  after : Hypernet d input output
  start : before.Vertex
  finish : after.Vertex
  localStep : Local before start after finish
  occurrence : Opening.Occurrence before G
  token : occurrence.ports start = v
  successor : StateIso ⟨H,(.search,w)⟩
    ⟨CompleteMatchCut.replaceWith occurrence.matchEmbedding occurrence.label after,
      (.search,CompleteMatchCut.replacePort occurrence.matchEmbedding occurrence.label after finish)⟩

namespace CutFactorization
variable {d I O} {G H : Hypernet d I O} {v : G.Vertex} {w : H.Vertex}
    (cut : CutFactorization G v H w)

/-- The constructed replacement is an actual original-machine successor. -/
theorem rewrite : Rewrite G v
    (CompleteMatchCut.replaceWith cut.occurrence.matchEmbedding cut.occurrence.label cut.after)
    (CompleteMatchCut.replacePort cut.occurrence.matchEmbedding cut.occurrence.label cut.after cut.finish) := by
  have actual := cut.occurrence.local_rewrite cut.localStep
  exact Eq.mp (congrArg (fun x => Rewrite G x
    (CompleteMatchCut.replaceWith cut.occurrence.matchEmbedding cut.occurrence.label cut.after)
    (CompleteMatchCut.replacePort cut.occurrence.matchEmbedding cut.occurrence.label cut.after cut.finish))
    cut.token) actual

/-- Factorization preserves the exact remaining finite execution spectrum. -/
theorem terminatesIn_iff (n : Nat) : TerminatesIn n ⟨H,(.search,w)⟩ ↔
    TerminatesIn n
      ⟨CompleteMatchCut.replaceWith cut.occurrence.matchEmbedding cut.occurrence.label cut.after,
        (.search,CompleteMatchCut.replacePort cut.occurrence.matchEmbedding cut.occurrence.label cut.after cut.finish)⟩ :=
  terminatesIn_iso cut.successor n

end CutFactorization

/-- Local, renamed, plugged and simultaneously expanded derivations all admit
the same finite cut factorization. No decomposition premise is required. -/
theorem Rewrite.cut_factorization {d I O} {G H : Hypernet d I O} {v w}
    (step : Rewrite G v H w) : Nonempty (CutFactorization G v H w) := by
  obtain ⟨J,K,A,B,a,b,localStep,f,token⟩ := step.local_occurrence
  have actual : Rewrite G (f.ports a) H w := by rw [token]; exact step
  obtain ⟨successor⟩ := f.rewrite_successor (.local localStep) actual
  exact ⟨⟨J,K,A,B,a,b,localStep,f,token,successor⟩⟩

end Combined
end Hypernets.Copying

import Hypernets.Copying.BoxPullWeakeningIdemRow
import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.CompleteMatchRealization
import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.AddressedWitness

/-! The exact two-Idem canonical row can be recognized inside an arbitrary
whole graph from its actual ordered incidences, then replaced through its
constructed finite complement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening.IdemRow
open Graph Opening

variable {d I O} {G : Hypernet d I O} {s : ShareSort}
  (row : Occurrence (CanonicalTree.atDepth s 2 d) G)

def attachedPort : (canonical d s).Vertex → G.Vertex := by
  cases d
  all_goals
    intro v
    exact match v with
    | .internal (.inl j) => row.ports (.input j)
    | .internal (.inr ⟨false,⟨false,v⟩⟩) => nomatch v
    | .internal (.inr ⟨false,⟨true,v⟩⟩) => nomatch v
    | .internal (.inr ⟨true,j⟩) => row.ports (.internal j)
    | .input i => Fin.elim0 i
    | .output j => row.ports (.output j)

def attachedEdge (weak : Bool → G.Edge) : (canonical d s).Edge → G.Edge := by
  cases d
  all_goals
    intro e
    exact match e with
    | ⟨false,⟨b,_⟩⟩ => weak b
    | ⟨true,e⟩ => row.edges e

theorem attached_tree_port (v : (CanonicalTree.atDepth s 2 d).Vertex) :
    attachedPort row (BoundarySerial.rightInsert
      (Net.Tensor.net (primitiveNet d (.weakening s)) (primitiveNet d (.weakening s)))
      (CanonicalTree.atDepth s 2 d) v) = row.ports v := by
  cases v with
  | internal v => cases d <;> rfl
  | input i => rw [CopyRule.serial_right_input]; cases d <;> rfl
  | output i => rw [Application.right_serial_output]; cases d <;> rfl

variable (weak : Bool → G.Edge) (weak_injective : Function.Injective weak)
  (disjoint : ∀ b e, weak b ≠ row.edges e)
  (labels : ∀ b, G.edgeLabel (weak b) = primitiveLabel d (.weakening s))
  (sources : ∀ b, G.source (weak b) = [])
  (targets : ∀ b, G.target (weak b) = [row.ports (.input
    (if b then ⟨1,by simp⟩ else ⟨0,by simp⟩))])

include labels in
theorem attachedLabel (e : (canonical d s).Edge) :
    LabelEquiv d ((canonical d s).edgeLabel e) (G.edgeLabel (attachedEdge row weak e)) := by
  cases d
  all_goals
    rcases e with ⟨b,e⟩
    cases b
    · rcases e with ⟨b,e⟩; cases b
      · change LabelEquiv _ (primitiveLabel _ (.weakening s)) (G.edgeLabel (weak false))
        rw [labels]; exact labelEquiv_refl _ _
      · change LabelEquiv _ (primitiveLabel _ (.weakening s)) (G.edgeLabel (weak true))
        rw [labels]; exact labelEquiv_refl _ _
    · exact row.label e

/-- Two genuine weakening edges attached to the two ordered inputs of the
unchanged canonical row determine its entire complete-label occurrence. -/
def attachedEmbedding : MatchEmbedding (canonical d s) G where
  ports := attachedPort row
  edges := attachedEdge row weak
  edge_injective := by
    cases d
    all_goals
      rintro ⟨b,e⟩ ⟨c,f⟩ eq
      cases b <;> cases c
      · rcases e with ⟨b,e⟩; rcases f with ⟨c,f⟩
        have bc : b = c := weak_injective eq
        subst c
        cases b
        all_goals
          have ef : e = f := Fin.ext (by have := e.isLt; have := f.isLt; omega)
          subst f; rfl
      · rcases e with ⟨b,e⟩; exact False.elim (disjoint b f eq)
      · rcases f with ⟨b,f⟩; exact False.elim (disjoint b e eq.symm)
      · have ef := row.edge_injective eq
        subst f; rfl
  primitive e p eq := (Search.primitive_equiv (attachedLabel row weak labels e) p).mp eq
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first
      | (rcases e with ⟨b,e⟩; cases b <;> exact (sources _).symm)
      | (change (((CanonicalTree.atDepth s 2 _).source e).map _).map _ = G.source (row.edges e)
         rw [List.map_map,← row.source]
         exact List.map_congr_left (fun v _ => attached_tree_port row v))
  target e := by
    cases d
    all_goals
      rcases e with ⟨b,e⟩
      cases b
      · rcases e with ⟨b,e⟩; cases b
        · change [row.ports (.input ⟨0,by simp⟩)] = G.target (weak false)
          exact (targets false).symm
        · change [row.ports (.input ⟨1,by simp⟩)] = G.target (weak true)
          exact (targets true).symm
      · change (((CanonicalTree.atDepth s 2 _).target e).map _).map _ = G.target (row.edges e)
        rw [List.map_map,← row.target]
        exact List.map_congr_left (fun v _ => attached_tree_port row v)

noncomputable def attachedOccurrence : Occurrence (canonical d s) G :=
  (attachedEmbedding row weak weak_injective disjoint labels sources targets).occurrence
    (attachedLabel row weak labels)

/-- The explicitly cut complement is focus-free whenever its actual host is;
the only fresh edge is the typed hole replacing the complete row. -/
theorem cut_free (f : Occurrence (canonical d s) G) (free : FocusFree G) :
    FocusFree (CompleteMatchCut.net f.matchEmbedding f.label) := by
  intro e
  cases e with
  | none => cases d <;> intro m eq <;> cases eq
  | some e => exact free e.val

/-- First Idem is grafted into the actual finite complement of the matched
row. Every host edge outside that complete row is retained literally. -/
noncomputable def cut_first (f : Occurrence (canonical d s) G) (free : FocusFree G) :
    FillingWitness ContractionIdempotence.template G
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label (ContractionIdempotence.left d s)) :=
  (((canonical_first d s).reboundary
      (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
      (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm).plug
      (CompleteMatchCut.net f.matchEmbedding f.label) (cut_free f free) none).congr
    (CompleteMatchCut.realization f.matchEmbedding f.label) (DeepIso.refl _)

/-- Second Idem uses the same original complement; its two endpoint graphs
are explicit finite replacements, not presumed contextual equivalents. -/
noncomputable def cut_second (f : Occurrence (canonical d s) G) (free : FocusFree G) :
    FillingWitness ContractionIdempotence.template
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label (ContractionIdempotence.left d s))
      (CompleteMatchCut.replaceWith f.matchEmbedding f.label (primitiveNet d (.weakening s))) :=
  ((second d s).reboundary
      (CompleteMatchCut.hole_input f.matchEmbedding f.label).symm
      (CompleteMatchCut.hole_output f.matchEmbedding f.label).symm).plug
      (CompleteMatchCut.net f.matchEmbedding f.label) (cut_free f free) none

end Hypernets.Copying.BoxPullWeakening.IdemRow

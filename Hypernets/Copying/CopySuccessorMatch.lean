import Hypernets.Copying.CopyPayloadRigidity

/-! Source data determining a complete copying successor, independently of the chosen tree boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening MatchEmbedding

/-- The selected input may be either source of its contraction. -/
def selectedSources {V : Type} (right : Bool) (selected other : V) : List V :=
  if right then [other,selected] else [selected,other]

structure SuccessorMatch {d I O k h} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d [.term] (environmentInterface k h)) where
  normal : NormalForm H
  payload : Occurrence H G
  active : G.Edge
  right : Bool
  other : G.Vertex
  active_label : G.edgeLabel active = primitiveLabel d (.contraction .term)
  active_source : G.source active = selectedSources right v other
  resolves : ∃ n, CopyTrace.Resolves G v (payload.edges normal.head) normal.primitive n

namespace SuccessorMatch
variable {d I O k h l j} {G : Hypernet d I O} {v}
  {H : Hypernet d [.term] (environmentInterface k h)}
  {K : Hypernet d [.term] (environmentInterface l j)}

def tail (a : SuccessorMatch G v H) := a.payload.edges a.normal.tail

theorem head_at (a : SuccessorMatch G v H) : HeadAt G v a.active (.contraction .term) := by
  refine ⟨a.active_label,?_⟩
  rw [a.active_source]
  cases a.right <;> simp [selectedSources]

theorem distinct (a : SuccessorMatch G v H) : v ≠ a.other := by
  have nodup := G.source_nodup a.active
  rw [a.active_source] at nodup
  cases eq : a.right <;> simpa [selectedSources,eq,ne_comm] using nodup

theorem frame_unique (a : SuccessorMatch G v H) (b : SuccessorMatch G v K) :
    a.active = b.active ∧ a.right = b.right ∧ a.other = b.other := by
  have same := (head_unique a.head_at b.head_at).1
  have src := a.active_source.symm.trans ((congrArg G.source same).trans b.active_source)
  refine ⟨same,?_⟩
  cases ha : a.right <;> cases hb : b.right <;> simp only [selectedSources,ha,hb,Bool.false_eq_true,↓reduceIte,List.cons.injEq] at src
  · exact ⟨rfl,src.2.1⟩
  · exact False.elim (b.distinct src.1)
  · exact False.elim (a.distinct src.1.symm)
  · exact ⟨rfl,src.1⟩

theorem payload_unique (a : SuccessorMatch G v H) (b : SuccessorMatch G v K) :
    PayloadRelated H K ∧ a.tail = b.tail := by
  obtain ⟨n,hn⟩ := a.resolves
  obtain ⟨m,hm⟩ := b.resolves
  exact a.normal.related b.normal a.payload b.payload (CopyTrace.resolves_unique hn hm).1

theorem output_length (a : SuccessorMatch G v H) : (G.target a.tail).length = (environmentInterface k h).length := by
  rw [tail,← a.payload.target,a.normal.tail_target,List.length_map,List.length_map,List.length_finRange]

def map {J L} {N : Hypernet d J L} (a : SuccessorMatch G v H) (f : Occurrence G N) : SuccessorMatch N (f.ports v) H where
  normal := a.normal
  payload := a.payload.comp f
  active := f.edges a.active
  right := a.right
  other := f.ports a.other
  active_label := f.matchEmbedding.primitive _ _ a.active_label
  active_source := by rw [← f.source,a.active_source]; cases a.right <;> rfl
  resolves := by obtain ⟨n,hn⟩ := a.resolves; exact ⟨n,CopyTrace.resolves_map f.matchEmbedding hn⟩
end SuccessorMatch
end Hypernets.Copying.CopyRule

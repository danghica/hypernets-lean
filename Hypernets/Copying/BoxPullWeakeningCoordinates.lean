import Hypernets.Copying.BoxPullWeakeningLaws
import Hypernets.Copying.SpliceBoundary
import Hypernets.Copying.PairBoundaryCoordinates

/-! Concrete port coordinates for BPullW's insertion of an unused resource.
These coordinates preserve the distinguished bound output in beta reductions. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph

/-- An interface-normalised version with unchanged graph carriers. -/
def adjoin {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    Hypernet d I (A ++ s.wire :: B) :=
  (insert G s).reboundary (List.append_nil I)
    (by simp only [List.append_nil,List.append_assoc,List.singleton_append])

/-- Every old output retains its index before the new slot and moves one
position to the right after that slot. -/
def oldOutput (A B : List Wire) (s : ShareSort) (i : Fin (A ++ B).length) :
    Fin (A ++ s.wire :: B).length :=
  ⟨if i.val < A.length then i.val else i.val + 1, by
    have := i.isLt
    simp only [List.length_append,List.length_cons] at *
    split <;> omega⟩

def weakeningOutput (A B : List Wire) (s : ShareSort) :
    Fin (A ++ s.wire :: B).length := ⟨A.length, by simp⟩

theorem inserted_old_output {I A B} (s : ShareSort) (i : Fin (A ++ B).length) :
    ((insertionBoundary I A B s).outputs.toFun ⟨false,i⟩).val =
      (oldOutput A B s i).val := by
  have repr := Net.Tensor.join_split A B i
  generalize split : Net.Tensor.split A B i = p at repr
  obtain ⟨b,j⟩ := p
  rw [← repr]
  cases b with
  | false =>
    have bound : j.val < A.length := j.isLt
    change ((InterfaceShuffle.bijection A B [s.wire] []).toFun
      ((InterfaceShuffle.original A B [s.wire] []).toFun (.inl (.inl j)))).val = _
    rw [PairBoundary.shuffle_component]
    simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
      Bijection.trans,Bijection.sum,Net.Tensor.join,oldOutput,bound]
  | true =>
    change ((InterfaceShuffle.bijection A B [s.wire] []).toFun
      ((InterfaceShuffle.original A B [s.wire] []).toFun (.inl (.inr j)))).val = _
    rw [PairBoundary.shuffle_component]
    simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
      Bijection.trans,Bijection.sum,Net.Tensor.join,oldOutput,Nat.add_assoc,Nat.add_comm]

theorem inserted_weakening_output {I A B} (s : ShareSort) :
    ((insertionBoundary I A B s).outputs.toFun ⟨true,(0 : Fin 1)⟩).val = A.length := by
  change ((InterfaceShuffle.bijection A B [s.wire] []).toFun
    ((InterfaceShuffle.original A B [s.wire] []).toFun (.inr (.inl 0)))).val = _
  rw [PairBoundary.shuffle_component]
  simp [InterfaceShuffle.shuffled,InterfaceShuffle.interchange,InterfaceShuffle.ports,
    Bijection.trans,Bijection.sum,Net.Tensor.join]

/-- The original component's actual embedding after equality transport. -/
def oldPort {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    G.Vertex → (adjoin G s).Vertex
  | .internal v => .internal ⟨false,v⟩
  | .input i => .input i
  | .output i => .output (oldOutput A B s i)

theorem oldPort_insert {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (v : G.Vertex) :
    Port.cast (List.append_nil I)
      (show (A ++ [s.wire]) ++ (B ++ []) = A ++ s.wire :: B by
        simp only [List.append_nil,List.append_assoc,List.singleton_append])
      (Net.Parallel.embed (Net.Tensor.family G (primitiveNet d (.weakening s)))
        (insertionBoundary I A B s) false v) = oldPort G s v := by
  cases v with
  | internal v => rfl
  | input i => rfl
  | output i => exact congrArg Port.output (Fin.ext (inserted_old_output s i))

theorem adjoin_source {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (e : G.Edge) : (adjoin G s).source ⟨false,e⟩ = (G.source e).map (oldPort G s) := by
  change ((G.source e).map _).map _ = _
  rw [List.map_map]
  exact List.map_congr_left (fun v _ => oldPort_insert G s v)

theorem adjoin_target {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (e : G.Edge) : (adjoin G s).target ⟨false,e⟩ = (G.target e).map (oldPort G s) := by
  change ((G.target e).map _).map _ = _
  rw [List.map_map]
  exact List.map_congr_left (fun v _ => oldPort_insert G s v)

/-- The new weakening still has no sources, at every representation allowance. -/
theorem adjoin_weakening_source {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (e : (primitiveNet d (.weakening s)).Edge) :
    (adjoin G s).source ⟨true,e⟩ = [] := by
  cases d <;> rfl

/-- The added edge targets exactly the new slot; no old resource is replaced. -/
theorem adjoin_weakening_target {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort)
    (e : (primitiveNet d (.weakening s)).Edge) :
    (adjoin G s).target ⟨true,e⟩ = [.output (weakeningOutput A B s)] := by
  cases d
  all_goals
    apply congrArg List.singleton
    apply congrArg Port.output
    exact Fin.ext (inserted_weakening_output s)

end Hypernets.Copying.BoxPullWeakening

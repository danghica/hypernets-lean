import Hypernets.Copying.CopyingInputPermutation
import Hypernets.Copying.CopyingResidualTree
import Hypernets.Copying.SharingTreeRealisation
import Hypernets.Copying.BoundarySafety
import Hypernets.Copying.SerialOccurrenceExtension

/-! Reindex the full ordered input interface of a genuine contraction tree.
The selected port becomes zero; all other original edges and ports remain. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph Opening

def exchange {a : Type} [DecidableEq a] (x y z : a) : a :=
  if z = x then y else if z = y then x else z

theorem exchange_involutive {a : Type} [DecidableEq a] (x y z : a) :
    exchange x y (exchange x y z) = z := by
  by_cases same : x = y
  · subst y; by_cases eq : z = x <;> simp [exchange,eq]
  · by_cases left : z = x
    · subst z; simp [exchange,Ne.symm same]
    · by_cases right : z = y
      · subst z; simp [exchange,Ne.symm same]
      · simp [exchange,left,right]

def swap (s : ShareSort) (m : Nat) (i j : Fin (List.replicate m s.wire).length) :
    TypedPermutation (List.replicate m s.wire) where
  bijection := ⟨exchange i j,exchange i j,exchange_involutive i j,exchange_involutive i j⟩
  typed i := by
    change (List.replicate m s.wire)[(exchange _ _ i).val] = (List.replicate m s.wire)[i.val]
    simp only [List.getElem_replicate]

theorem reordered_graph {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) :
    SharingTreeGraph s m (net (T.atDepth 0) p) where
  labels e := by
    change primitiveLabel 0 (T.net.edgeLabel e) = primitiveLabel 0 (.weakening s) ∨
      primitiveLabel 0 (T.net.edgeLabel e) = primitiveLabel 0 (.contraction s)
    rcases T.labels e with h | h
    · exact .inl (congrArg (primitiveLabel 0) h)
    · exact .inr (congrArg (primitiveLabel 0) h)
  acyclic {es} path := by
    have original := ((iso (T.atDepth 0) p).path_iff es).mp
      (by simpa only [iso,Bijection.refl,List.map_id_fun,id_eq] using path)
    have lower : ∀ {xs : List (T.atDepth 0).Edge}, (T.atDepth 0).Path xs → T.net.Path xs := by
      intro xs h
      induction h with
      | single e => exact Net.Path.single (G := T.net) e
      | cons adj tail ih => exact Net.Path.cons (G := T.net) adj ih
    exact T.acyclic (lower original)

noncomputable def reordered {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) : ContractionTree s m :=
  (reordered_graph T p).tree

theorem reordered_label {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) (e) :
    (reordered T p).net.edgeLabel e = T.net.edgeLabel e := by
  apply primitiveLabel_injective 0
  exact (reordered_graph T p).primitive_label e

/-- The reindexed tree has the same edge carrier. Its occurrence maps the
new input positions back to the original ordered inputs using the inverse. -/
noncomputable def occurrence {s m} (T : ContractionTree s m) (p : TypedPermutation (List.replicate m s.wire)) (d : Nat) :
    Occurrence ((reordered T p).atDepth d) (T.atDepth d) where
  ports
    | .input i => .input (p.bijection.invFun i)
    | .output i => .output i
    | .internal v => .internal v
  internals := id
  edges := id
  internal_map _ := rfl
  internal_injective := fun _ _ h => h
  edge_injective := fun _ _ h => h
  internal_label _ := rfl
  label e := by
    change LabelEquiv d (primitiveLabel d ((reordered T p).net.edgeLabel e)) (primitiveLabel d (T.net.edgeLabel e))
    rw [reordered_label]
    exact labelEquiv_refl _ _
  source e := by
    change ((T.net.source e).map (ports (T.atDepth 0) p).toFun).map _ = T.net.source e
    rw [List.map_map]
    exact List.map_id'' (fun v => by cases v <;> simp [ports,p.bijection.left_inv]) _
  target e := by
    change ((T.net.target e).map (ports (T.atDepth 0) p).toFun).map _ = T.net.target e
    rw [List.map_map]
    exact List.map_id'' (fun v => by cases v <;> simp [ports,p.bijection.left_inv]) _

theorem occurrence_input {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) (d : Nat)
    (i : Fin (List.replicate m s.wire).length) :
    (occurrence T p d).ports (.input i) = .input (p.bijection.invFun i) := rfl

theorem occurrence_output {s m} (T : ContractionTree s m)
    (p : TypedPermutation (List.replicate m s.wire)) (d : Nat) :
    ∀ i, (occurrence T p d).ports (.output i) = .output i := fun _ => rfl

end Hypernets.Copying.CopyingInputPermutation

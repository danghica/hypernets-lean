import Hypernets.Copying.WeakeningRows
import Hypernets.Copying.NullaryParallelSerial

/-! Original weakening forests, including the use-major resource order.
These isomorphisms expose rowwise Idem proofs inside actual distributors. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening
open Graph

/-- The original zero-use distributor, with its empty input equality exposed. -/
def forest (d : Nat) (s : ShareSort) (k : Nat) : Hypernet d [] (List.replicate k s.wire) :=
  (Distributor.atDepth s k 0 d).reboundary (by simp) rfl

/-- A finite family of zero-use forests is exactly the zero-use forest on its
ordered global interface. The boundary bijection specifies every resource. -/
def forest_parallel_iso {A : Type} (d : Nat) (s : ShareSort) (m : A → Nat) (k : Nat)
    (B : Net.Parallel.Boundary (fun _ : A => []) (fun a => List.replicate (m a) s.wire)
      [] (List.replicate k s.wire)) (finite : Enumeration A) :
    DeepIso (Net.Parallel.net (fun a => forest d s (m a)) B finite) (forest d s k) where
  vertices := by
    cases d
    all_goals exact {
      toFun := fun ⟨_,_,v⟩ => Fin.elim0 v
      invFun := fun ⟨_,v⟩ => Fin.elim0 v
      left_inv := fun ⟨_,_,v⟩ => Fin.elim0 v
      right_inv := fun ⟨_,v⟩ => Fin.elim0 v }
  edges := by
    cases d
    all_goals exact {
      toFun := fun ⟨a,j,e⟩ => ⟨⟨(B.outputs.toFun ⟨a,⟨j.val,by simp⟩⟩).val,by simpa using (B.outputs.toFun ⟨a,⟨j.val,by simp⟩⟩).isLt⟩,e⟩
      invFun := fun ⟨j,e⟩ =>
        let p := B.outputs.invFun ⟨j.val,by simp⟩
        ⟨p.1,⟨⟨p.2.val,by simpa using p.2.isLt⟩,e⟩⟩
      left_inv := by
        rintro ⟨a,j,e⟩
        change (fun p : Σ a, Fin (List.replicate (m a) s.wire).length =>
          (⟨p.1,⟨⟨p.2.val,by simpa using p.2.isLt⟩,e⟩⟩ :
            (Net.Parallel.net (fun a => forest _ s (m a)) B finite).Edge))
          (B.outputs.invFun (B.outputs.toFun ⟨a,⟨j.val,by simp⟩⟩)) = _
        rw [B.outputs.left_inv]
      right_inv := by
        rintro ⟨j,e⟩
        change (fun i : Fin (List.replicate k s.wire).length =>
          (⟨⟨i.val,by simpa using i.isLt⟩,e⟩ : (forest _ s k).Edge))
          (B.outputs.toFun (B.outputs.invFun ⟨j.val,by simp⟩)) = _
        rw [B.outputs.right_inv] }
  internal_label v := by cases d <;> rcases v with ⟨a,j,v⟩ <;> exact Fin.elim0 v
  edge_label e := by cases d <;> rcases e with ⟨a,j,e⟩ <;> exact labelEquiv_refl _ _
  source e := by
    cases d <;> rcases e with ⟨a,j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rfl
  target e := by
    cases d <;> rcases e with ⟨a,j,e⟩
    all_goals
      have z : e = (0 : Fin 1) := Subsingleton.elim (α := Fin 1) _ _
      subst e
      rfl

/-- The original distributor is literally its ordered forest of canonical
rows at every allowance, including zero resources or zero uses. -/
def distributor_rows (d : Nat) (s : ShareSort) (k m : Nat) :
    DeepIso (Distributor.atDepth s k m d)
      (Net.Parallel.net (fun _ : Fin k => CanonicalTree.atDepth s m d)
        (Distributor.boundary s k m) (Enumeration.fin k)) := by
  cases d
  all_goals exact {
    vertices := Bijection.refl _
    edges := Bijection.refl _
    internal_label _ := rfl
    edge_label _ := labelEquiv_refl _ _
    source e := by
      change ((Distributor.atDepth s k m _).source e).map (Port.map id) = _
      rw [show (Port.map id : (Distributor.atDepth s k m _).Vertex → _) = id by funext v; cases v <;> rfl, List.map_id]
      rcases e with ⟨a,e⟩
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    target e := by
      change ((Distributor.atDepth s k m _).target e).map (Port.map id) = _
      rw [show (Port.map id : (Distributor.atDepth s k m _).Vertex → _) = id by funext v; cases v <;> rfl, List.map_id]
      rcases e with ⟨a,e⟩
      apply List.map_congr_left
      intro v _
      cases v <;> rfl }


/-- Feeding every input of the actual distributor with the original zero-use
forest is isomorphic to independently feeding its actual canonical rows. -/
noncomputable def distributor_feeding (d : Nat) (s : ShareSort) (k m : Nat) :
    DeepIso
      (Serial.net (forest d s (k*m)) (Distributor.atDepth s k m d))
      (Net.Parallel.net
        (fun _ : Fin k => Serial.net (forest d s m) (CanonicalTree.atDepth s m d))
        (NullaryParallelSerial.afterBoundary (Distributor.boundary s k m)) (Enumeration.fin k)) :=
  (Serial.congr
    (forest_parallel_iso d s (fun _ : Fin k => m) (k*m)
      (NullaryParallelSerial.beforeBoundary (Distributor.boundary s k m)) (Enumeration.fin k)).symm
    (distributor_rows d s k m)).trans
      (NullaryParallelSerial.iso (fun _ : Fin k => forest d s m)
        (fun _ => CanonicalTree.atDepth s m d) (Distributor.boundary s k m) (Enumeration.fin k))

end Hypernets.Copying.Weakening

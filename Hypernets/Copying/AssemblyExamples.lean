import Hypernets.Copying.Examples
import Hypernets.Copying.Distributor
import Hypernets.Copying.Serial

namespace Hypernets.Copying.Examples

/-- Three resources used twice occupy interleaved input positions. -/
theorem distributor_input_order (s : ShareSort) :
    ((Distributor.boundary s 3 2).inputs.toFun ⟨0,⟨0,by simp⟩⟩).val = 0 ∧
    ((Distributor.boundary s 3 2).inputs.toFun ⟨0,⟨1,by simp⟩⟩).val = 3 ∧
    ((Distributor.boundary s 3 2).inputs.toFun ⟨1,⟨0,by simp⟩⟩).val = 1 ∧
    ((Distributor.boundary s 3 2).inputs.toFun ⟨1,⟨1,by simp⟩⟩).val = 4 ∧
    ((Distributor.boundary s 3 2).inputs.toFun ⟨2,⟨0,by simp⟩⟩).val = 2 ∧
    ((Distributor.boundary s 3 2).inputs.toFun ⟨2,⟨1,by simp⟩⟩).val = 5 := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Interleaving does not connect different resources' trees. -/
theorem distributor_separation (s : ShareSort) (e f : Fin 3) :
    ¬ (Distributor.net s 2 2).Adjacent ⟨0,e⟩ ⟨1,f⟩ := by
  intro h
  have eq := Distributor.adjacent_tag s 2 2 h
  exact (by decide : (0 : Fin 2) ≠ 1) eq

/-- A single-use distributor retains a weakening and a contraction. -/
theorem distributor_single_use (s : ShareSort) :
    (Distributor.net s 1 1).edgeLabel ⟨0,0⟩ = .weakening s ∧
    (Distributor.net s 1 1).edgeLabel ⟨0,1⟩ = .contraction s := by
  exact ⟨rfl,rfl⟩

/-- Zero uses retains one weakening for each resource. -/
theorem distributor_no_uses (s : ShareSort) :
    (Distributor.net s 2 0).edgeLabel ⟨0,0⟩ = .weakening s ∧
    (Distributor.net s 2 0).edgeLabel ⟨1,0⟩ = .weakening s := by
  exact ⟨rfl,rfl⟩

/-- A concrete atom-interface assembly. This is wiring, not a store reduction. -/
def instanceStore (d : Nat) : Hypernet d [.term] [.term] :=
  Serial.net (primitiveNet d .instanceEdge) (primitiveNet d .store)

theorem instanceStore_focusFree (d : Nat) : FocusFree (instanceStore d) := by
  apply Serial.focusFree_net <;> intro e
  all_goals cases d <;> intro mode eq <;> cases eq

theorem instanceStore_holeFree (d : Nat) : HoleFree (instanceStore d) := by
  apply Serial.holeFree_net <;> intro e
  all_goals cases d <;> intro hole eq <;> cases eq

end Hypernets.Copying.Examples

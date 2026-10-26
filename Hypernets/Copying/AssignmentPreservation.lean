import Hypernets.Copying.AssignmentExecution

/-! Assignment changes the store's term connection, not its atom identity.
Discarding is represented by weakening, not by deleting the old heap. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Assignment
open Graph

def afterValueVertex {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : G.Vertex → (after T G).Vertex := by
  cases d <;> exact Net.Expansion.insert (afterPattern _ h O) (afterFill T G) .value

theorem updated_content {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (after T G).target (afterStore T G) = [afterValueVertex T G (.input 0)] := by cases d <;> rfl

theorem value_sources {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) :
    (after T G).source (afterValue T G e) = (G.source e).map (afterValueVertex T G) := by cases d <;> rfl

theorem value_targets {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (e : G.Edge) :
    (after T G).target (afterValue T G e) = (G.target e).map (afterValueVertex T G) := by cases d <;> rfl

theorem value_output_order {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (i : Fin O.length) :
    afterValueVertex T G (.output i) = outputPort h O i := by
  cases d
  all_goals
    change Net.Expansion.insert (afterPattern _ h O) (afterFill T G) .value (.output i) = _
    simp [Net.Expansion.insert,Net.Expansion.host,Net.targetPort,
    afterPattern,afterFrame,afterTarget,valueOutputs,outputPort,Port.map]

def discardOld {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (after T G).Edge := by
  cases d <;> exact ⟨.discardOld,(0 : Fin 1)⟩
def discardInstance {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) : (after T G).Edge := by
  cases d <;> exact ⟨.discardInstance,(0 : Fin 1)⟩

theorem old_content_weakened {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (after T G).edgeLabel (discardOld T G) = primitiveLabel d (.weakening .term) ∧
    (after T G).target (discardOld T G) = [.output ⟨0,by simp [outputs]⟩] := by
  cases d <;> exact ⟨rfl,rfl⟩

theorem instance_weakened {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) :
    (after T G).edgeLabel (discardInstance T G) = primitiveLabel d (.weakening .term) ∧
    (after T G).target (discardInstance T G) = (after T G).source (afterInstance T G) := by
  cases d <;> exact ⟨rfl,rfl⟩

theorem other_references_preserved {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (i : Fin h) :
    beforeTreeVertex T G (.input ⟨i.val+1,by simp⟩) = inputPort h O i.succ ∧
    afterTreeVertex T G (.input ⟨i.val+1,by simp⟩) = inputPort h O i.succ := by
  cases d <;> constructor
  all_goals
    first
    | change Net.Expansion.insert (beforePattern _ h O) (beforeFill T G) .tree (.input ⟨i.val+1,by change i.val+1 < (List.replicate (h+1) Wire.atom).length; simp⟩) = _
    | change Net.Expansion.insert (afterPattern _ h O) (afterFill T G) .tree (.input ⟨i.val+1,by change i.val+1 < (List.replicate (h+1) Wire.atom).length; simp⟩) = _
    simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,
      beforePattern,afterPattern,beforeFrame,afterFrame,beforeSource,afterSource,otherInputs,inputPort,Port.map]


/-- Attaching an arbitrary old-content continuation retains every edge of that continuation. -/
def withContents {d h O K} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (C : Hypernet d (outputs O) K) : Hypernet d (inputs h) K := Serial.net (after T G) C

theorem old_contents_retained {d h O K} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (C : Hypernet d (outputs O) K) (e : C.Edge) :
    (withContents T G C).edgeLabel (Serial.rightEdge _ _ e) = C.edgeLabel e := Serial.rightEdge_label _ _ _

/-- Arbitrary surrounding content cannot redirect the already resolved reference. -/
theorem attached_store_unique {d h O K} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O)
    (C : Hypernet d (outputs O) K) {e m}
    (res : StoreTrace.Resolves (withContents T G C) (Serial.leftEdge _ _ (afterInstance T G)) e m) :
    e = Serial.leftEdge _ _ (afterStore T G) := by
  obtain ⟨n,_,run⟩ := resolves_both T G
  exact (StoreTrace.resolves_unique res (StoreTrace.resolves_serial_left (after T G) C run)).1
end Hypernets.Copying.Assignment

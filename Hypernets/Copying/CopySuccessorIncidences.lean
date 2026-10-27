import Hypernets.Copying.CopySuccessorSource

/-! The literal reduct's ordered incidence lists, before comparing independent matches. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyRule
open Graph Opening
variable {d n k h} (T : ContractionTree .term (n+1)) (H : Hypernet d [.term] (environmentInterface k h))

def keptTreeEdge (e : T.net.Edge) : (after T H).Edge :=
  Serial.leftEdge _ _ ⟨true,Serial.leftEdge _ _ (residualTreeEdge T d e)⟩
def addedWeakening : (after T H).Edge :=
  Serial.leftEdge _ _ ⟨true,Serial.leftEdge _ _ (residualWeakening T d)⟩

theorem active_source (e : H.Edge) : (after T H).source (leftEdge T H e) = (H.source e).map (activeInsert T H) := by
  cases d
  all_goals
    change (((H.source e).map _).map _).map _ = _
    rw [List.map_map,List.map_map]; rfl

theorem active_target (e : H.Edge) : (after T H).target (leftEdge T H e) = (H.target e).map (activeInsert T H) := by
  cases d
  all_goals
    change (((H.target e).map _).map _).map _ = _
    rw [List.map_map,List.map_map]; rfl

theorem retained_source (e : H.Edge) : (after T H).source (rightEdge T H e) = (H.source e).map (retainedInsert T H) := by
  cases d
  all_goals
    change ((((H.source e).map _).map _).map _).map _ = _
    rw [List.map_map,List.map_map,List.map_map]; rfl

theorem retained_target (e : H.Edge) : (after T H).target (rightEdge T H e) = (H.target e).map (retainedInsert T H) := by
  cases d
  all_goals
    change ((((H.target e).map _).map _).map _).map _ = _
    rw [List.map_map,List.map_map,List.map_map]; rfl

theorem kept_tree_source (e : T.net.Edge) : (after T H).source (keptTreeEdge T H e) = (T.net.source e).map (treeInsert T H) := by
  cases d
  all_goals
    change (((((T.net.source e).map _).map _).map _).map _).map _ = _
    rw [List.map_map,List.map_map,List.map_map,List.map_map]; rfl

theorem kept_tree_target (e : T.net.Edge) : (after T H).target (keptTreeEdge T H e) = (T.net.target e).map (treeInsert T H) := by
  cases d
  all_goals
    change (((((T.net.target e).map _).map _).map _).map _).map _ = _
    rw [List.map_map,List.map_map,List.map_map,List.map_map]; rfl

theorem added_weakening_source : (after T H).source (addedWeakening T H) = [] := by cases d <;> rfl
theorem added_weakening_target : (after T H).target (addedWeakening T H) = [treeInsert T H (.input ⟨0,by simp⟩)] := by
  cases d <;> rfl
end Hypernets.Copying.CopyRule

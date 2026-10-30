import Hypernets.Copying.SharingTreeSerialJoin

/-! The original serial constructor supplies its two actual component
occurrences and their exact common ordered junction. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial
open Graph Opening
variable {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)

def leftOccurrence : Occurrence G (net G H) := by
  cases d <;> exact Occurrence.expand (pattern _ I J K) (filling G H) false

def rightOccurrence : Occurrence H (net G H) := by
  cases d <;> exact Occurrence.expand (pattern _ I J K) (filling G H) true

theorem occurrence_boundary (i : Fin J.length) :
    (leftOccurrence G H).ports (.output i) = (rightOccurrence G H).ports (.input i) := by
  cases d
  all_goals
    change Net.Expansion.host _ _ ((pattern _ I J K).targetPort false _) =
      Net.Expansion.host _ _ ((pattern _ I J K).sourcePort true _)
    exact congrArg (Net.Expansion.host _ _) (interface_connection _ I J K i)

theorem leftOccurrence_input (i : Fin I.length) :
    (leftOccurrence G H).ports (.input i) = .input i := by
  cases d
  all_goals
    change Net.Expansion.host (pattern _ I J K) (filling G H) ((pattern _ I J K).sourcePort false _) = .input i
    simp [Net.Expansion.host,Net.sourcePort,pattern,Port.map,List.getElem_map,List.getElem_finRange]

end Hypernets.Copying.Serial

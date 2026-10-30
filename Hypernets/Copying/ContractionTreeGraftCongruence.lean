import Hypernets.Copying.ContractionTreeGraft
import Hypernets.Graph.ExpansionIso

/-! Independent recursive representation changes preserve the literal input
graft and its ordered external boundary. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph

/-- Both grafted components may change recursive representation, while the
selected original input and every external boundary position stay fixed. -/
noncomputable def congr {d a b O s}
    {P Q : Hypernet d (List.replicate a (ShareSort.wire s)) [ShareSort.wire s]}
    {G H : Hypernet d (List.replicate (b+1) (ShareSort.wire s)) O}
    (p : DeepIso P Q) (g : DeepIso G H) (j : Fin (b+1)) :
    DeepIso (net P G j) (net Q H j) := by
  apply Net.ExpansionIso.iso
  intro e
  cases d <;> cases e
  all_goals first | exact p | exact g
end Hypernets.Copying.ContractionTree.Graft

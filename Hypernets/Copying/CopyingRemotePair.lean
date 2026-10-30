import Hypernets.Copying.CopyingRemotePairTransfer
import Hypernets.Copying.CopyingRemotePositiveRaw
import Hypernets.Copying.CopyingRemoteZero

/-! Exhaustive literal and independently represented remote-copy diagrams.
The distinguished and positive shallow inputs are proved separately. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote
open Graph Combined ContractionTree

/-- Every original ordered shallow input has actual opposite rewrites and a
constructed original residual with independently proved sharing corrections. -/
theorem literalDiagrams : LiteralDiagrams := by
  intro d m n k h P T H j copyable free
  by_cases zero : j.val = 0
  · have eq : j = (0 : Fin (n+1)) := Fin.ext zero
    subst j
    exact Zero.raw_diagram P T H copyable free
  · have positive : 0 < j.val := by omega
    cases n with
    | zero => have bound := j.isLt; omega
    | succ n =>
      obtain ⟨X,Y,l,r,⟨p⟩⟩ := Positive.raw_diagram P T H j copyable free positive
      exact ⟨X,Y,l,r,⟨CopyingTemplate.TwoSidedResidual.ofResidual p⟩⟩
end Hypernets.Copying.CopyingRemote

namespace Hypernets.Copying.CopyingTemplate.Pair
open Graph Combined ContractionTree

/-- A complete original copying pair at any selected graft input has a real
one-copy-per-side remote diagram. There is no matching, robustness, or residual
hypothesis; independent recursive representation changes are accounted for. -/
theorem graft_diagram {d m n k h} (P : ContractionTree .term (m+1))
    {G H : Hypernet d (List.replicate (n+1) .term) (environmentInterface k h)}
    (rel : Pair G H) (j : Fin (n+1)) :
    ∃ X Y : Hypernet d (List.replicate ((m+1)+n) .term) (environmentInterface k h),
      Rewrite (Graft.net (s := .term) (P.atDepth d) G j) (.input ⟨0,by simp; omega⟩) X (.input ⟨0,by simp; omega⟩) ∧
      Rewrite (Graft.net (s := .term) (P.atDepth d) H j) (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩) ∧
      Nonempty (TwoSidedResidual X (.input ⟨0,by simp; omega⟩) Y (.input ⟨0,by simp; omega⟩)) :=
  CopyingRemote.Pair.graft_diagram_of CopyingRemote.literalDiagrams P rel j
end Hypernets.Copying.CopyingTemplate.Pair

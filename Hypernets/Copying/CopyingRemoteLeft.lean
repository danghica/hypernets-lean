import Hypernets.Copying.ContractionTreeGraftSerial
import Hypernets.Copying.ContractionTreeGraftWitness
import Hypernets.Copying.CopyingRetainedContext

/-! The literal upstream copying successor first receives a proved exact
sharing correction, then retains one genuine downstream copying instance. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingRemote.Left
open Graph ContractionTree
variable {d m b k h : Nat}
    (P : ContractionTree .term (m+1)) (T : ContractionTree .term (b+1))
    (H : Hypernet d [.term] (environmentInterface k h)) (j : Fin (b+1))

def middleBefore : Hypernet d (List.replicate (m+b+1) .term) (environmentInterface k h) :=
  CopyingRetainedContext.after H (Graft.net (s := .term) (a := m) (CopyRule.residual P d) (CopyRule.before T H) j)

def middleAfter : Hypernet d (List.replicate (m+b+1) .term) (environmentInterface k h) :=
  CopyingRetainedContext.after H (Graft.net (s := .term) (a := m) (CopyRule.residual P d) (CopyRule.after T H) j)

/-- Closing the selected upstream input is normalized by the independently
proved sharing algebra. The whole graph retains both original payloads,
all residual inputs and the unchanged resource distributors. -/
noncomputable def leading (free : FocusFree H) :
    FillingWitness SharingTreeAlgebra.template
      (CopyRule.after (Graft.copyTree P T j) H) (middleBefore P T H j) := by
  have tree := Graft.residual_graft_net_witness P T j d
  have branch := FillingWitness.serial tree (FillingWitness.refl H free)
  have actual := branch.congr (DeepIso.refl _)
    (Graft.SerialRight.iso (CopyRule.residual P d) (T.atDepth d) H j).symm
  exact CopyingRetainedContext.witness H free actual

/-- The middle relation is the actual original downstream copying template
in its computed common context, not an assumed commutation of two rewrites. -/
noncomputable def original (copyable : Copyable H) (free : FocusFree H) :
    FillingWitness CopyingTemplate.template (middleBefore P T H j) (middleAfter P T H j) := by
  have residualFree : FocusFree (CopyRule.residual P d) :=
    by
      intro e
      rcases ((CopyRule.residualTree P).sharingTreeGraph d).labels e with label | label
      all_goals
        change (CopyRule.residual P d).edgeLabel e = _ at label
        rw [label]
        cases d <;> intro mode bad <;> cases bad
  have inside := Graft.witness (T := CopyingTemplate.template) (s := .term) (a := m) (FillingWitness.refl (CopyRule.residual P d) residualFree)
    (FillingWitness.of_rel (T := CopyingTemplate.template) 0 (CopyingTemplate.literal T H copyable free)) j
  exact CopyingRetainedContext.witness H free inside
end Hypernets.Copying.CopyingRemote.Left

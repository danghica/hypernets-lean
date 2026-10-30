import Hypernets.Copying.ContractionTreeGraft
import Hypernets.Graph.ExpansionAssociativity

/-! Exact reassociation of simultaneous expansion through a literal graft.
Both original component families retain their complete ordered interfaces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph
variable {s : ShareSort} {a b d : Nat} {O : List Wire}
    (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) O) (j : Fin (b+1))
    (F : (e : (net P G j).Edge) → Hypernet d
      ((alphabet d).signature.input ((net P G j).edgeLabel e))
      ((alphabet d).signature.output ((net P G j).edgeLabel e)))

def expansionLeft (e : P.Edge) : Hypernet d
    ((alphabet d).signature.input (P.edgeLabel e)) ((alphabet d).signature.output (P.edgeLabel e)) := by
  cases d <;> exact F ⟨false,e⟩
def expansionRight (e : G.Edge) : Hypernet d
    ((alphabet d).signature.input (G.edgeLabel e)) ((alphabet d).signature.output (G.edgeLabel e)) := by
  cases d <;> exact F ⟨true,e⟩

def expansionIso : DeepIso ((net P G j).expand F)
    (net (P.expand (expansionLeft P G j F)) (G.expand (expansionRight P G j F)) j) := by
  cases d
  all_goals
    have assoc := DeepIso.ofIso (Net.ExpansionAssoc.iso (pattern s a b O j _) (filling P G j)
      (fun e x => F ⟨e,x⟩))
    have same : Net.ExpansionAssoc.flat (pattern s a b O j _) (filling P G j) (fun e x => F ⟨e,x⟩) = F := by
      funext e; cases e; rfl
    rw [same] at assoc
    apply assoc.trans
    apply Net.ExpansionIso.iso
    intro e
    cases e <;> exact DeepIso.refl _

end Hypernets.Copying.ContractionTree.Graft

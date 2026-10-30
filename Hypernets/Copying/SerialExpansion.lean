import Hypernets.Copying.Serial
import Hypernets.Copying.FillingWitness
import Hypernets.Graph.ExpansionAssociativity

/-! Simultaneous expansion reassociates through the original serial graph
constructor with completely arbitrary typed component families. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Serial
open Graph
variable {d I J O} (G : Hypernet d I J) (H : Hypernet d J O)
    (F : (e : (net G H).Edge) → Hypernet d
      ((alphabet d).signature.input ((net G H).edgeLabel e))
      ((alphabet d).signature.output ((net G H).edgeLabel e)))

def expansionLeft (e : G.Edge) : Hypernet d
    ((alphabet d).signature.input (G.edgeLabel e)) ((alphabet d).signature.output (G.edgeLabel e)) := by
  cases d <;> exact F ⟨false,e⟩

def expansionRight (e : H.Edge) : Hypernet d
    ((alphabet d).signature.input (H.edgeLabel e)) ((alphabet d).signature.output (H.edgeLabel e)) := by
  cases d <;> exact F ⟨true,e⟩

/-- This is graph-associativity of actual expansions, not a sharing equation
or an assumed operational congruence. -/
def expansionIso : DeepIso ((net G H).expand F)
    (net (G.expand (expansionLeft G H F)) (H.expand (expansionRight G H F))) := by
  cases d
  all_goals
    have assoc := DeepIso.ofIso (Net.ExpansionAssoc.iso (pattern _ I J O) (filling G H) (fun e x => F ⟨e,x⟩))
    have same : Net.ExpansionAssoc.flat (pattern _ I J O) (filling G H) (fun e x => F ⟨e,x⟩) = F := by
      funext e
      cases e
      rfl
    rw [same] at assoc
    apply assoc.trans
    apply Net.ExpansionIso.iso
    intro e
    cases e <;> exact DeepIso.refl _

end Hypernets.Copying.Serial

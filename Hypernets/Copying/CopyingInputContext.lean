import Hypernets.Copying.CopyingInputPermutation
import Hypernets.Copying.CombinedPadding

/-! Input permutation is an actual one-hole graph context. Consequently it
transports original rewrites with their exact input positions and rule premises. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingInputPermutation
open Graph Combined

def frame (d : Nat) (I O : List Wire) (p : TypedPermutation I) : Hypernet d I O :=
  net (primitiveNet d (.hole ⟨0,I,O⟩)) p

def frameEdge (d : Nat) (I O : List Wire) (p : TypedPermutation I) : (frame d I O p).Edge := by
  cases d <;> exact (0 : Fin 1)

/-- The plugged payload uses precisely the original interfaces of the hole. -/
def inFrame {d I O} (G : Hypernet d I O) (p : TypedPermutation I) :=
  G.reboundary (by cases d <;> rfl : I = (alphabet d).signature.input ((frame d I O p).edgeLabel (frameEdge d I O p)))
    (by cases d <;> rfl : O = (alphabet d).signature.output ((frame d I O p).edgeLabel (frameEdge d I O p)))

/-- Delete only the empty corolla carrier introduced by the permutation context. -/
noncomputable def frameIso {d I O} (G : Hypernet d I O) (p : TypedPermutation I) :
    DeepIso ((frame d I O p).plug (frameEdge d I O p) (inFrame G p)) (net G p) := by
  cases d
  all_goals
    simp only [inFrame,Net.reboundary_refl]
    apply DeepIso.ofIso
    refine { vertices := Net.PlugUnit.leftVertices G
             edges := Net.PlugUnit.leftEdges G
             internal_label := ?_
             edge_label := ?_
             source := ?_
             target := ?_ }
    · rintro (x | y); exact nomatch x; rfl
    · rintro (x | y); exact False.elim (Net.PlugUnit.noEdge x); rfl
    · rintro (x | y)
      · exact False.elim (Net.PlugUnit.noEdge x)
      · change ((G.source y).map _).map _ = (G.source y).map _
        rw [List.map_map]
        apply List.map_congr_left
        intro v _; cases v <;>
          simp [Net.Replacement.insert,Net.Replacement.host,Net.PlugUnit.leftVertices,
            Net.sourcePort,Net.targetPort,frame,frameEdge,net,ports,primitiveNet,Net.corolla,
            List.getElem_map,List.getElem_finRange,Port.map]
    · rintro (x | y)
      · exact False.elim (Net.PlugUnit.noEdge x)
      · change ((G.target y).map _).map _ = (G.target y).map _
        rw [List.map_map]
        apply List.map_congr_left
        intro v _; cases v <;>
          simp [Net.Replacement.insert,Net.Replacement.host,Net.PlugUnit.leftVertices,
            Net.sourcePort,Net.targetPort,frame,frameEdge,net,ports,primitiveNet,Net.corolla,
            List.getElem_map,List.getElem_finRange,Port.map]

/-- Reindexing input ports preserves each actual original rewrite and moves
the active and resumed positions by the same typed permutation. -/
theorem rewrite {d I O} {G H : Hypernet d I O} (p : TypedPermutation I)
    (i j : Fin I.length) (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (net G p) (.input (p.bijection.toFun i))
      (net H p) (.input (p.bijection.toFun j)) := by
  cases d
  all_goals
    have lifted := Rewrite.plug (frame _ I O p) (frameEdge _ I O p) step
    have lifted := lifted.rename
      (by simpa only [inFrame,Net.reboundary_refl] using frameIso G p)
      (by simpa only [inFrame,Net.reboundary_refl] using frameIso H p)
    simpa [Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,frame,frameEdge,
      net,ports,primitiveNet,Net.corolla,List.getElem_map,List.getElem_finRange,Port.map]
      using lifted

end Hypernets.Copying.CopyingInputPermutation

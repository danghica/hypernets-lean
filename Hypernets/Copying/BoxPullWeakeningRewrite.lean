import Hypernets.Copying.BoxPullWeakeningCoordinates
import Hypernets.Copying.ParallelContextPlug
import Hypernets.Copying.CombinedPadding

/-! Contextual transport of an actual original rewrite past a separate
weakening edge. Both the active and resumed boundary coordinates are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

def insertionContext (d : Nat) (I A B : List Wire) (s : ShareSort) :=
  insert (primitiveNet d (.hole ⟨0,I,A ++ B⟩)) s

def insertionHole (d : Nat) (I A B : List Wire) (s : ShareSort) :
    (insertionContext d I A B s).Edge := by cases d <;> exact ⟨false,(0 : Fin 1)⟩

/-- Filling the one real hole gives exactly the inserted graph, up to its
finite carrier names. The separate weakening is retained by the isomorphism. -/
noncomputable def insertion_plug {d I A B} (G : Hypernet d I (A ++ B)) (s : ShareSort) :
    DeepIso ((insertionContext d I A B s).plug (insertionHole d I A B s)
      (G.reboundary (by cases d <;> rfl) (by cases d <;> rfl))) (insert G s) := by
  cases d with
  | zero =>
    simp only [Net.reboundary_refl]
    exact (DeepIso.ofIso (ParallelPair.plug_left (insertionBoundary I A B s)
      (primitiveNet 0 (.hole ⟨0,I,A ++ B⟩)) (primitiveNet 0 (.weakening s)) (0 : Fin 1) G)).trans
      (ParallelPair.congr _ (DeepIso.ofIso (Net.corolla_plug_iso (primitiveLabel 0 (.hole ⟨0,I,A ++ B⟩)) G)) (DeepIso.refl _))

  | succ n =>
    simp only [Net.reboundary_refl]
    exact (DeepIso.ofIso (ParallelPair.plug_left (insertionBoundary I A B s)
      (primitiveNet (n+1) (.hole ⟨0,I,A ++ B⟩)) (primitiveNet (n+1) (.weakening s)) (0 : Fin 1) G)).trans
      (ParallelPair.congr _ (DeepIso.ofIso (Net.corolla_plug_iso (primitiveLabel (n+1) (.hole ⟨0,I,A ++ B⟩)) G)) (DeepIso.refl _))

/-- Any original boundary-to-boundary rewrite lifts through this ordinary
parallel context. The proof uses only original plugging and renaming rules. -/
theorem insert_rewrite {d I A B} {G H : Hypernet d I (A ++ B)}
    (s : ShareSort) (i j : Fin I.length)
    (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (insert G s) (.input ⟨i.val,by simp⟩)
      (insert H s) (.input ⟨j.val,by simp⟩) := by
  cases d with
  | zero =>
    have lifted := Rewrite.plug (insertionContext 0 I A B s) (insertionHole 0 I A B s) step
    have lifted := lifted.rename (by simpa only [Net.reboundary_refl] using insertion_plug G s)
      (by simpa only [Net.reboundary_refl] using insertion_plug H s)
    have source (F : Hypernet 0 I (A ++ B)) (x : Fin I.length) :
        Net.Replacement.insert (insertionContext 0 I A B s) (insertionHole 0 I A B s) F (.input x) =
          .input ⟨x.val,by simp [primitiveSignature]⟩ := by
      simp [Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,insertionContext,insertionHole,
        insert,Net.Parallel.net,Net.Parallel.incidence,Net.Tensor.family,primitiveNet,Net.corolla,
        insertionBoundary,Net.Parallel.embed,Net.Tensor.ports,Net.Tensor.join,List.getElem_map,
        List.getElem_finRange,Port.map]
    rw [source G i,source H j] at lifted
    exact lifted

  | succ n =>
    have lifted := Rewrite.plug (insertionContext (n+1) I A B s) (insertionHole (n+1) I A B s) step
    have lifted := lifted.rename (by simpa only [Net.reboundary_refl] using insertion_plug G s)
      (by simpa only [Net.reboundary_refl] using insertion_plug H s)
    have source (F : Hypernet (n+1) I (A ++ B)) (x : Fin I.length) :
        Net.Replacement.insert (insertionContext (n+1) I A B s) (insertionHole (n+1) I A B s) F (.input x) =
          .input ⟨x.val,by simp [primitiveSignature]⟩ := by
      simp [Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,insertionContext,insertionHole,
        insert,Net.Parallel.net,Net.Parallel.incidence,Net.Tensor.family,primitiveNet,Net.corolla,
        insertionBoundary,Net.Parallel.embed,Net.Tensor.ports,Net.Tensor.join,List.getElem_map,
        List.getElem_finRange,Port.map]
    rw [source G i,source H j] at lifted
    exact lifted

theorem adjoin_rewrite {d I A B} {G H : Hypernet d I (A ++ B)}
    (s : ShareSort) (i j : Fin I.length)
    (step : Rewrite G (.input i) H (.input j)) :
    Rewrite (adjoin G s) (.input i) (adjoin H s) (.input j) :=
  rewrite_reboundary (List.append_nil I)
    (by simp only [List.append_nil,List.append_assoc,List.singleton_append])
    (insert_rewrite s i j step)

end Hypernets.Copying.BoxPullWeakening

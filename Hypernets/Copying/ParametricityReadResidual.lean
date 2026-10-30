import Hypernets.Copying.ParametricityReadFullCopy
import Hypernets.Copying.ParametricityClosedCopyPair
import Hypernets.Copying.ParametricityPointedCut

/-! Pointed residual certificates for the content-copy stage of private
readback. Both links sit in the actual computed read complement, retaining
its store, discarded instance and arbitrary atom contraction tree. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Parametricity.ReadTail.FullCopy
open Graph Combined Opening
open BoxPullWeakening (PointedWitness)
variable {h} (T : ContractionTree .atom (h+1)) (d : Nat)

theorem afterRead_focusFree : FocusFree (afterRead T d) :=
  Serial.focusFree_net (Dereference.focusFree_sides T d).2 (by
    cases d <;> intro e m eq <;> cases eq)

/-- The intermediate is the exact old read complement, with the complete
second-copy reduct inserted at its original two ordered content inputs. -/
noncomputable def middle : Hypernet d (Dereference.inputs h) [] :=
  CompleteMatchCut.replaceWith (occurrence T d).matchEmbedding (occurrence T d).label
    (ClosedCopyPair.selectedMiddle (ContractionTree.canonical .term 2) (numeral d) 1)

noncomputable def middlePoint : (middle T d).Vertex :=
  CompleteMatchCut.replacePort (occurrence T d).matchEmbedding (occurrence T d).label
    (ClosedCopyPair.selectedMiddle (ContractionTree.canonical .term 2) (numeral d) 1) (.input ⟨1,by simp⟩)

/-- The two actual numeral edges are now independent, with input zero still
attached to the store and input one still attached to the active read result. -/
noncomputable def separated : Hypernet d (Dereference.inputs h) [] :=
  CompleteMatchCut.replaceWith (occurrence T d).matchEmbedding (occurrence T d).label
    (ClosedCopyPair.selectedPair (numeral d) 1)

noncomputable def separatedPoint : (separated T d).Vertex :=
  CompleteMatchCut.replacePort (occurrence T d).matchEmbedding (occurrence T d).label
    (ClosedCopyPair.selectedPair (numeral d) 1) (.input ⟨1,by simp⟩)

theorem resume_input : resume T d = .input ⟨0,by simp [Dereference.inputs]⟩ :=
  CompleteMatchCut.replace_input (occurrence T d).matchEmbedding (occurrence T d).label
    ⟨1,by simp⟩ ⟨0,by simp [Dereference.inputs]⟩ (token T d)

theorem middlePoint_input : middlePoint T d = .input ⟨0,by simp [Dereference.inputs]⟩ :=
  CompleteMatchCut.replace_input (occurrence T d).matchEmbedding (occurrence T d).label
    ⟨1,by simp⟩ ⟨0,by simp [Dereference.inputs]⟩ (token T d)

theorem separatedPoint_input : separatedPoint T d = .input ⟨0,by simp [Dereference.inputs]⟩ :=
  CompleteMatchCut.replace_input (occurrence T d).matchEmbedding (occurrence T d).label
    ⟨1,by simp⟩ ⟨0,by simp [Dereference.inputs]⟩ (token T d)

/-- The original copying template corrects the residual shared stored value.
The token is its actual old reader attachment inside the retained complement. -/
noncomputable def copyingResidual :
    PointedWitness CopyingTemplate.template (reduct T d) (resume T d)
      (middle T d) (middlePoint T d) :=
  CompleteMatchCut.inputWitness (occurrence T d).matchEmbedding (occurrence T d).label
    (afterRead_focusFree T d)
    (ClosedCopyPair.selectedCopying (ContractionTree.canonical .term 2) (numeral d) 1
      (.constant d (.nat 1)) (by cases d <;> intro e m eq <;> cases eq)) ⟨1,by simp⟩

/-- The following independent GC correction has the same literal pointed
attachment. It removes only the unused closed copy, not the retained store. -/
noncomputable def garbageResidual :
    PointedWitness GarbageCollection.template (middle T d) (middlePoint T d)
      (separated T d) (separatedPoint T d) :=
  CompleteMatchCut.inputWitness (occurrence T d).matchEmbedding (occurrence T d).label
    (afterRead_focusFree T d)
    (ClosedCopyPair.selectedGarbage (ContractionTree.canonical .term 2) (numeral d) 1
      (.constant d (.nat 1)) (by cases d <;> intro e m eq <;> cases eq)) ⟨1,by simp⟩

end Hypernets.Copying.Parametricity.ReadTail.FullCopy

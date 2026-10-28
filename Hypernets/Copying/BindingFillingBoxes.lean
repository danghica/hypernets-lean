import Hypernets.Copying.BindingFillingPlug

/-! Exact common-context corollas for boxed recursive filling certificates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.FillingWitness
open Graph
variable {T : PreTemplate}

/-- Reindexing the external interface leaves the entire common context intact. -/
theorem reboundary_context {d I O J K} {G H : Hypernet d I O}
    (w : FillingWitness T G H) (hi : I = J) (ho : O = K) :
    (w.reboundary hi ho).context = w.context.reboundary hi ho := by
  cases hi; cases ho
  have aux (A B : Hypernet d I O) (ha : A = G) (hb : B = H)
      (eq : FillingWitness T A B = FillingWitness T G H) :
      (Eq.mpr eq w).context = w.context := by
    cases ha; cases hb
    have proof : eq = rfl := Subsingleton.elim _ _
    cases proof
    rfl
  exact (aux (G.reboundary rfl rfl) (H.reboundary rfl rfl)
    (Net.reboundary_refl G) (Net.reboundary_refl H)
    (by rw [Net.reboundary_refl,Net.reboundary_refl])).trans (Net.reboundary_refl w.context).symm

/-- Rebuilding literal boxes retains one original box over the common body
context, even when its boundary and edge carriers have other representations. -/
def boxedCopies_contextCopy {d I O n k h}
    {L R : Hypernet d [.term] (environmentInterface (n+k) h)}
    {G H : Hypernet (d+1) I O} (w : FillingWitness T L R)
    (l : LabelCopy G (.inr ⟨n,k,h,L⟩)) (r : LabelCopy H (.inr ⟨n,k,h,R⟩)) :
    LabelCopy (w.boxedCopies l r).context (.inr ⟨n,k,h,w.context⟩) := by
  change LabelCopy (w.boxed.reboundary l.input l.output).context _
  rw [reboundary_context]
  exact (LabelCopy.corolla (d := d+1) (.inr ⟨n,k,h,w.context⟩)).reboundary l.input l.output

end Hypernets.Copying.FillingWitness

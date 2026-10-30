import Hypernets.Copying.AllocationEnabled
import Hypernets.Copying.BoxPullWeakeningResidual
import Hypernets.Copying.RetainedFrameTransfer

/-! Replacing a retained primitive edge preserves every original shallow and
deep template component. The paired successor is a genuine recursive filling,
pointed at the unchanged original host wire. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined
namespace LabelCopy

/-- Replacing the unique edge of an actual corolla leaves precisely the
replacement graph, including all of its ordered boundary attachments. -/
noncomputable def plugIso {d} {a : (alphabet d).Symbol}
    {G : Hypernet d ((alphabet d).signature.input a) ((alphabet d).signature.output a)}
    (copy : LabelCopy G a)
    (H : Hypernet d ((alphabet d).signature.input a) ((alphabet d).signature.output a)) :
    DeepIso (G.plug copy.edge (H.reboundary
      (congrArg ((alphabet d).signature.input) copy.edge_label).symm
      (congrArg ((alphabet d).signature.output) copy.edge_label).symm)) H := by
  let f := copy.iso (LabelCopy.corolla a) (labelEquiv_refl d a)
  have moved := f.plugHost copy.edge
    (congrArg ((alphabet d).signature.input) copy.edge_label)
    (congrArg ((alphabet d).signature.output) copy.edge_label)
    (labelEquiv_refl d)
    (H.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
      (congrArg ((alphabet d).signature.output) copy.edge_label).symm)
  have normalized : DeepIso (G.plug copy.edge (H.reboundary
      (congrArg ((alphabet d).signature.input) copy.edge_label).symm
      (congrArg ((alphabet d).signature.output) copy.edge_label).symm))
      ((Net.corolla (alphabet d).signature a).plug (0 : Fin 1) H) := by
    simpa only [f,LabelCopy.iso,LabelCopy.corolla,reboundary_comp,Net.reboundary_refl] using moved
  exact normalized.trans (DeepIso.ofIso (Net.corolla_plug_iso a H))

end LabelCopy

namespace Allocation.Retained
variable {d I O} (C : Hypernet d I O)
    {F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (e : C.Edge) (label : C.edgeLabel e = primitiveLabel d (.operation (.unary .ref)))
    (copy : LabelCopy (F e) (C.edgeLabel e))

/-- The selected source corolla is replaced by the whole original allocation
prefix. Every other component is literally the original supplied filler. -/
noncomputable def family := BoxPermutation.PointedFilling.replace C F e (Allocation.filler C e label)

/-- Canonical allocation of a retained ref corolla has the same successor as
changing only its member of the original filling family. -/
noncomputable def canonicalIso (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length) :
    StateIso (Allocation.canonical (C.expand F) ⟨e,copy.edge⟩
      (copy.edge_label.trans label) (Net.Expansion.insert C F e (.input i)))
      ⟨C.expand (family C (F := F) e label),(.search,Net.Expansion.host C (family C (F := F) e label) (C.sourcePort e i))⟩ := by
  let A := Allocation.filler C e label
  let K := family C (F := F) e label
  have chosen : K e = A := BoxPermutation.PointedFilling.replace_selected C F e A
  have others : ∀ b, b ≠ e → F b = K b := by
    intro b ne
    exact (BoxPermutation.PointedFilling.replace_other C F e A b ne).symm
  have localIso : StateIso (Allocation.canonical (F e) copy.edge
      (copy.edge_label.trans label) (.input i)) ⟨A,(.search,.input i)⟩ := by
    refine ⟨?_,rfl,rfl⟩
    have eq : Allocation.filler (F e) copy.edge (copy.edge_label.trans label) =
        A.reboundary (congrArg ((alphabet d).signature.input) copy.edge_label).symm
          (congrArg ((alphabet d).signature.output) copy.edge_label).symm := by
      unfold A Allocation.filler
      rw [reboundary_comp]
    change DeepIso ((F e).plug copy.edge _) A
    rw [eq]
    exact copy.plugIso A
  have transport (H) (eq : K e = H)
      (localIso : StateIso (Allocation.canonical (F e) copy.edge
        (copy.edge_label.trans label) (.input i)) ⟨H,(.search,.input i)⟩) :
      StateIso (Allocation.canonical (F e) copy.edge
        (copy.edge_label.trans label) (.input i)) ⟨K e,(.search,.input i)⟩ := by
    cases eq; exact localIso
  have selected := transport A chosen localIso
  exact Replacement.expand_result C F K e others copy.edge
    (Allocation.filler (F e) copy.edge (copy.edge_label.trans label)) (.input i) (.input i) selected

include copy in
/-- A rooted ref request executes to the shared changed-family representation.
Only the selected original ref corolla is replaced; the operand remains external. -/
theorem rooted_rewrite {v : C.Vertex}
    (head : MatchEmbedding.HeadAt C v e (.operation (.unary .ref)))
    {j : Fin I.length}
    (rooted : Search.RootedFrom (C.expand F) j (.rewrite,Net.Expansion.host C F v)) :
    Rewrite (C.expand F) (Net.Expansion.host C F v)
      (C.expand (family C (F := F) e label))
      (Net.Expansion.host C (family C (F := F) e label) v) := by
  let i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length :=
    ⟨0,by rw [label,primitive_input]; decide⟩
  have input : C.sourcePort e i = v := by
    have row := Search.operation_source head.1 head.2
    simp [Net.sourcePort,row,i]
  have chosen : MatchEmbedding.HeadAt (C.expand F) (Net.Expansion.host C F v)
      ⟨e,copy.edge⟩ (.operation (.unary .ref)) := by
    refine ⟨copy.edge_label.trans label,?_⟩
    change Net.Expansion.host C F v ∈ (C.expand F).source ⟨e,copy.retained.edge⟩
    rw [copy.retained.source_eq]
    exact List.mem_map_of_mem head.2
  obtain ⟨H,w,step⟩ := Allocation.rooted_enabled (C.expand F) chosen rooted
  obtain ⟨canonicalStep⟩ := rewrite_allocation_canonical step chosen
  let iso := canonicalIso C e label copy i
  have normalized : StateIso (Allocation.canonical (C.expand F) ⟨e,copy.edge⟩
      chosen.1 (Net.Expansion.host C F v))
      ⟨C.expand (family C (F := F) e label),
        (.search,Net.Expansion.host C (family C (F := F) e label) v)⟩ := by
    simpa only [Net.Expansion.insert,input] using iso
  let result := canonicalStep.symm.trans normalized
  have moved := step.rename (DeepIso.refl _) result.graph
  simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id,
    result.vertex] using moved

end Allocation.Retained

namespace Allocation.Retained
open BoxPullWeakening (PointedWitness)
variable {T : PreTemplate} {d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge T C L R e) (free : FocusFree C)
    (e : C.Edge) (label : C.edgeLabel e = primitiveLabel d (.operation (.unary .ref)))

/-- Actual allocation prefixes carry no focus, including their canonical
atom contraction and weakening. -/
theorem filler_free : FocusFree (Allocation.filler C e label) := by
  unfold Allocation.filler
  exact Allocation.prefix_labels _ d (by intro m eq; cases eq) (by intro m eq; cases eq)
    (by intro m eq; cases eq) (by intro m eq; cases eq)

/-- Replace only the selected ref component by the same genuine allocation
prefix on both sides; every other original recursive certificate is retained. -/
noncomputable def witnesses : ∀ b, FillingWitness T
    (family C (F := L) e label b) (family C (F := R) e label b) := by
  classical
  intro b
  by_cases same : b = e
  · subst b
    simpa only [family,BoxPermutation.PointedFilling.replace_selected] using
      (FillingWitness.refl (T := T) (Allocation.filler C e label) (filler_free C e label))
  · simpa only [family,BoxPermutation.PointedFilling.replace_other C L e _ b same,
      BoxPermutation.PointedFilling.replace_other C R e _ b same] using
      FillingWitness.originalEdge (cert b) free

/-- The residual keeps the selected old host token, even when the stable
argument is a lambda inside a multi-input shallow family. -/
noncomputable def pointed (v : C.Vertex) :
    PointedWitness T (C.expand (family C (F := L) e label))
      (Net.Expansion.host C (family C (F := L) e label) v)
      (C.expand (family C (F := R) e label))
      (Net.Expansion.host C (family C (F := R) e label) v) where
  filling := FillingWitness.expand C (witnesses C cert free e label)
  point := Net.Expansion.host C (fun b => (witnesses C cert free e label b).context) v
  left := congrArg Prod.snd (FillingWitness.expand_leftPosition C (witnesses C cert free e label) .search v)
  right := congrArg Prod.snd (FillingWitness.expand_rightPosition C (witnesses C cert free e label) .search v)

end Allocation.Retained
end Hypernets.Copying

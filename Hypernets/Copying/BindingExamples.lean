import Hypernets.Copying.BindingClosure
import Hypernets.Copying.ValueExamples
import Hypernets.Copying.BindingInvariance
import Hypernets.Copying.BindingPathCorrespondence

set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Examples
open Graph

/-- Every original translated term is binding-free because it has no holes. -/
theorem translated_bindingFree {k h} (t : Term k h) : BindingFree (Translation.term t) :=
  BindingFree.of_holeFree _ (Translation.term_focusFree t) (Translation.term_holeFree t)

/-- A stand-alone hole has no positive return path to its source. -/
theorem hole_bindingFree (d : Nat) (h : Hole) : BindingFree (primitiveNet d (.hole h)) := by
  refine ⟨?_,?_⟩
  · intro e; cases d <;> intro m eq <;> cases eq
  · have sh : ShallowBindingFree (primitiveNet d (.hole h)) := by
      intro e f _ _ _ path
      obtain ⟨g,⟨v,hv,hw⟩,_⟩ := path
      cases d <;>
        obtain ⟨i,_,rfl⟩ := List.mem_map.mp hv <;>
        obtain ⟨j,_,eq⟩ := List.mem_map.mp hw <;> cases eq
    cases d with
    | zero => exact sh
    | succ d => exact ⟨sh,fun _ => trivial⟩

/-- Every hole used by the term translation has a source, irrespective of the
sizes of the variable and atom environments. -/
theorem term_hole_sourced (d name k h : Nat) :
    BindingFree.SourcedHole (Site.shallow
      (primitiveNet d (.hole ⟨name,[.term],environmentInterface k h⟩)) (by cases d <;> exact (0 : Fin 1))) := by
  cases d <;> exact ⟨⟨_,rfl⟩,⟨.input (0 : Fin 1),by simp [primitiveNet,Net.corolla]⟩⟩

/-- Two distinct holes joined by an atom wire. The first has no inputs. -/
def zeroInputContext : Hypernet 0 [] [] := Serial.pattern 0 [] [.atom] []

/-- A weakening followed by an instance: no external inputs and one atom output. -/
def zeroInputReplacement : Hypernet 0 [] [.atom] :=
  Serial.net (primitiveNet 0 (.weakening .term)) (primitiveNet 0 .instanceEdge)

theorem zeroInputContext_bindingFree : BindingFree zeroInputContext := by
  refine ⟨?_,?_⟩
  · intro e m eq; cases e <;> cases eq
  · intro e f _ src _ path
    cases e with
    | false =>
      obtain ⟨v,hv⟩ := src
      simp [zeroInputContext,Serial.pattern] at hv
    | true =>
      obtain ⟨g,⟨v,hv,_⟩,_⟩ := path
      simp [zeroInputContext,Serial.pattern] at hv

theorem zeroInputReplacement_bindingFree : BindingFree zeroInputReplacement := by
  apply BindingFree.of_holeFree
  · apply Serial.focusFree_net <;> intro e m eq <;> cases eq
  · apply Serial.holeFree_net <;> intro e h eq <;> cases eq


/-- The counterexample host is a context: its two hole labels are distinct. -/
theorem zeroInputContext_unique_holes (e f : zeroInputContext.Edge) (h : Hole)
    (he : zeroInputContext.edgeLabel e = primitiveLabel 0 (.hole h))
    (hf : zeroInputContext.edgeLabel f = primitiveLabel 0 (.hole h)) : e = f := by
  have eq := he.trans hf.symm
  cases e <;> cases f <;> first | rfl | cases eq

/-- Under the literal source-based definition, the sourced-hole hypothesis in
Appendix-E closure cannot be removed for arbitrary hole interfaces. -/
theorem zeroInput_plug_not_bindingFree :
    ¬ BindingFree (zeroInputContext.plug false zeroInputReplacement) := by
  intro free
  let a : (zeroInputContext.plug false zeroInputReplacement).Edge := .inr ⟨true,(0 : Fin 1)⟩
  let b : (zeroInputContext.plug false zeroInputReplacement).Edge := .inl ⟨true,by intro h; cases h⟩
  apply free.2 a b (by trivial) (by
    exact ⟨.internal (.inr (.inl (0 : Fin 1))),by
      change _ ∈ [_]
      exact List.mem_cons_self⟩) ⟨_,rfl⟩
  refine ⟨b,⟨.internal (.inl (0 : Fin 1)),?_,?_⟩,.refl b⟩
  all_goals change _ ∈ [_]; exact List.mem_cons_self

/-- The unrestricted closure claim fails even for finite focus-free graphs.
This is not a counterexample to closure at translated term holes. -/
theorem unrestricted_hole_closure_false : ¬
    (∀ {d I O} (C : Hypernet d I O) (e : C.Edge)
      (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e))),
      HoleLabel d (C.edgeLabel e) →
      BindingFree C → BindingFree H → BindingFree (C.plug e H)) := by
  intro closed
  exact zeroInput_plug_not_bindingFree (closed zeroInputContext false zeroInputReplacement
    ⟨_,rfl⟩ zeroInputContext_bindingFree zeroInputReplacement_bindingFree)

end Hypernets.Copying.Examples

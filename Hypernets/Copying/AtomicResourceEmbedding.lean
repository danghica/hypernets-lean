import Hypernets.Copying.SelectedResourceEmbedding
import Hypernets.Copying.OccurrenceTensorMap

/-! Injective old-resource occurrences in all original atomic translation clauses. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Weakening.Atomic
open Graph Opening

/-- The zero-use forest retains each old weakening under an injective index map. -/
def forestEmbedding (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) :
    Occurrence (Distributor.atDepth s n 0 d) (Distributor.atDepth s m 0 d) where
  ports
    | .internal v => .internal ⟨ρ v.1,v.2⟩
    | .input i => Fin.elim0 i
    | .output i => .output ⟨(ρ ⟨i.val,by simpa using i.isLt⟩).val,by simp⟩
  internals v := ⟨ρ v.1,v.2⟩
  edges e := ⟨ρ e.1,e.2⟩
  internal_map _ := rfl
  internal_injective := by rintro ⟨a,v⟩ ⟨b,w⟩ eq; exact Fin.elim0 v
  edge_injective := by
    rintro ⟨a,e⟩ ⟨b,f⟩ eq
    have ab := inj (congrArg Sigma.fst eq)
    change a = b at ab
    subst b
    exact congrArg (Sigma.mk a) (eq_of_heq (Sigma.mk.inj eq).2)
  internal_label v := Fin.elim0 v.2
  label _ := labelEquiv_refl _ _
  source e := by
    rcases e with ⟨i,e⟩
    have z : e = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst e
    rfl
  target e := by
    rcases e with ⟨i,e⟩
    have z : e = 0 := Subsingleton.elim (α := Fin 1) _ _
    subst e
    rfl

theorem forestEmbedding_output (s : ShareSort) (d : Nat) {n m}
    (ρ : Fin n → Fin m) (inj : Function.Injective ρ) (i : Fin n) :
    (forestEmbedding s d ρ inj).ports (.output ⟨i.val,by simp⟩) = .output ⟨(ρ i).val,by simp⟩ := rfl

/-- Variables retain the selected contraction and every old atom weakening. -/
noncomputable def variableMap {d k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j)
    (rinj : Function.Injective ρ) (ainj : Function.Injective α) (i : Fin k) :
    Occurrence (Translation.variableTerm d h i) (Translation.variableTerm d j (ρ i)) := by
  unfold Translation.variableTerm
  exact ((SelectedResource.embedding .term d ρ rinj i).tensorMap
    (forestEmbedding .atom d α ainj)).castInterfaces _ _ _ _

/-- The atom's original instance edge is retained before the selected row. -/
noncomputable def atom {d k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j)
    (rinj : Function.Injective ρ) (ainj : Function.Injective α) (a : Fin h) :
    Occurrence (Translation.atom d k a) (Translation.atom d l (α a)) := by
  unfold Translation.atom
  exact ((forestEmbedding .term d ρ rinj).tensorMap
    ((SelectedResource.embedding .atom d α ainj a).serialPrefix (primitiveNet d .instanceEdge)
      (SelectedResource.embedding_input .atom d α ainj a))).castInterfaces _ _ _ _

/-- Constants retain their original operation edge and both old weakening forests. -/
noncomputable def constant {d k h l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j)
    (rinj : Function.Injective ρ) (ainj : Function.Injective α) (c : Constant) :
    Occurrence (Translation.constant d k h c) (Translation.constant d l j c) := by
  unfold Translation.constant
  exact (((forestEmbedding .term d ρ rinj).tensorMap
    (Occurrence.ofIso (DeepIso.refl (primitiveNet d (.operation (.const c)))))).tensorMap
    (forestEmbedding .atom d α ainj)).castInterfaces _ _ _ _

end Hypernets.Copying.Weakening.Atomic

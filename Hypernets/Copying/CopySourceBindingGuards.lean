import Hypernets.Copying.RetainedBindingGuards

/-! Every original copying footprint protects its entire output interface.
The selected input supplies a sourced contraction and its original tree path;
all copyable primitive operations and arbitrary lambda boxes are covered. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem BindingGuardedOutputs.iso {d I O} {A B : Hypernet d I O} (f : DeepIso A B)
    (guard : BindingGuardedOutputs A) : BindingGuardedOutputs B := by
  intro i
  obtain ⟨e,g,binding,⟨v,source⟩,path,target⟩ := guard i
  let m := MatchEmbedding.ofDeepIso f
  refine ⟨f.edges.toFun e,f.edges.toFun g,
    (BindingFree.bindingLabel_equiv d (f.edge_label e)).mp binding,
    ⟨m.ports v,m.source_mem source⟩,path.map m.edges m.adjacent,?_⟩
  exact m.target_mem target

theorem BindingGuardedOutputs.serialRight {d I J K} (G : Hypernet d I J) (H : Hypernet d J K)
    (guard : BindingGuardedOutputs H) : BindingGuardedOutputs (Serial.net G H) := by
  intro i
  obtain ⟨e,g,binding,⟨v,source⟩,path,target⟩ := guard i
  let f := MatchEmbedding.serialRight G H
  refine ⟨f.edges e,f.edges g,?_,⟨f.ports v,f.source_mem source⟩,
    path.map f.edges f.adjacent,?_⟩
  · change BindingLabel d ((Serial.net G H).edgeLabel (Serial.rightEdge G H e))
    rw [Serial.rightEdge_label]
    exact binding
  · cases d
    all_goals
      change Port.output i ∈ (H.target g).map _
      apply List.mem_map.mpr
      refine ⟨Port.output i,target,?_⟩
      simp [f,MatchEmbedding.serialRight,Serial.rightEdge,Net.Expansion.insert,Net.targetPort,
        Serial.pattern,Net.Expansion.host,Port.map]

/-- A positive-input sharing tree has a sourced contraction ancestry to its
unique output, independent of the tree presentation and unused siblings. -/
theorem CopyRule.tree_bindingGuarded {n} (T : ContractionTree .term (n+1)) (d : Nat) :
    BindingGuardedOutputs (CopyRule.tree T d) := by
  intro i
  have eq : i = (0 : Fin 1) := by apply Fin.ext; have h := i.isLt; change i.val < 1 at h; change i.val = 0; omega
  subst i
  obtain ⟨e,m,source,path⟩ := T.input_reaches_root ⟨0,by simp⟩
  refine ⟨e,T.root,?_,⟨.input ⟨0,by simp⟩,source⟩,?_,T.root_output⟩
  · rcases T.labels e with weak | contr
    · have mem := List.mem_map_of_mem (f := T.net.vertexLabel) source
      dsimp only [Net.vertexLabel] at mem
      rw [T.net.source_typed,weak] at mem
      exact False.elim (List.not_mem_nil mem)
    · change BindingLabel d (primitiveLabel d (T.net.edgeLabel e))
      rw [contr]
      cases d <;> trivial
  · have convert {a b m} (p : Trace T.net.Adjacent a b m) : Ancestor (CopyRule.tree T d) a b := by
      induction p with
      | refl => exact .refl _
      | step adj rest ih => exact .step adj ih
    exact convert path

/-- A component whose output producer also consumes the input extends the
original binding tree guard by its actual serial attachment. -/
theorem CopyRule.before_flat_bindingGuarded {d n k h} (T : ContractionTree .term (n+1))
    (G : Hypernet d [.term] (environmentInterface k h))
    (flat : ∀ i : Fin (environmentInterface k h).length, ∃ e : G.Edge,
      Port.input 0 ∈ G.source e ∧ Port.output i ∈ G.target e) :
    BindingGuardedOutputs (CopyRule.before T G) := by
  intro i
  obtain ⟨e,g,binding,⟨v,source⟩,path,target⟩ := CopyRule.tree_bindingGuarded T d (0 : Fin 1)
  obtain ⟨a,input,output⟩ := flat i
  let l := MatchEmbedding.serialLeft (CopyRule.tree T d) G
  let r := MatchEmbedding.serialRight (CopyRule.tree T d) G
  have join : l.ports (.output 0) = r.ports (.input 0) := by
    cases d <;> rfl
  refine ⟨l.edges e,r.edges a,?_,⟨l.ports v,l.source_mem source⟩,?_,?_⟩
  · change BindingLabel d ((Serial.net (CopyRule.tree T d) G).edgeLabel (Serial.leftEdge _ _ e))
    rw [Serial.leftEdge_label]
    exact binding
  · exact (path.map l.edges l.adjacent).trans
      (.step ⟨l.ports (.output 0),l.target_mem target,join.symm ▸ r.source_mem input⟩ (.refl _))
  · cases d
    all_goals
      change Port.output i ∈ (G.target a).map _
      apply List.mem_map.mpr
      refine ⟨Port.output i,output,?_⟩
      simp [r,MatchEmbedding.serialRight,Serial.rightEdge,Net.Expansion.insert,Net.targetPort,
        Serial.pattern,Net.Expansion.host,Port.map]

/-- The box itself guards every free environment output of a lambda payload. -/
theorem lambdaPayload_bindingGuarded {d k h}
    (body : Hypernet d [.term] (environmentInterface (k+1) h)) :
    BindingGuardedOutputs (lambdaPayload body) := by
  apply BindingGuardedOutputs.serialRight
  intro i
  refine ⟨(0 : Fin 1),(0 : Fin 1),by trivial,⟨.input (0 : Fin 1),List.mem_cons_self⟩,.refl _,?_⟩
  exact List.mem_map_of_mem (List.mem_finRange i)

/-- Every copyable payload, including active operations, arbitrary boxed bodies
and independent recursive representations, has a guarded copying source. -/
theorem CopyRule.before_bindingGuarded {d n k h} (T : ContractionTree .term (n+1))
    {G : Hypernet d [.term] (environmentInterface k h)} (copyable : Copyable G) :
    BindingGuardedOutputs (CopyRule.before T G) := by
  induction copyable with
  | instanceEdge d =>
    apply before_flat_bindingGuarded
    intro i
    cases d <;> exact ⟨(0 : Fin 1),List.mem_cons_self,List.mem_map_of_mem (List.mem_finRange i)⟩
  | constant d c =>
    apply before_flat_bindingGuarded
    intro i
    exact Fin.elim0 i
  | application d =>
    apply before_flat_bindingGuarded
    intro i
    cases d <;> exact ⟨(0 : Fin 1),List.mem_cons_self,List.mem_map_of_mem (List.mem_finRange i)⟩
  | unary d o =>
    apply before_flat_bindingGuarded
    intro i
    cases d <;> exact ⟨(0 : Fin 1),List.mem_cons_self,List.mem_map_of_mem (List.mem_finRange i)⟩
  | binary d o =>
    apply before_flat_bindingGuarded
    intro i
    cases d <;> exact ⟨(0 : Fin 1),List.mem_cons_self,List.mem_map_of_mem (List.mem_finRange i)⟩
  | lambda body => exact (lambdaPayload_bindingGuarded body).serialRight (tree T _) _
  | rename iso copyable ih => exact ih.iso (before_congr (Net.Iso.refl T.net) iso)
end Hypernets.Copying

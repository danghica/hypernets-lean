import Hypernets.Copying.OperationalTemplates
import Hypernets.Copying.FramedFillingTransfer
import Hypernets.Copying.BindingClosure

/-! Input safety of the original operational templates.  The finite prefixes
below retain the stable-argument premises and count every search transition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph Combined

namespace Allocation
/-- The three search transitions that precede reference creation for an arbitrary
stable argument, rather than only a translated constant. -/
theorem entry_trace {d O} (G : Hypernet d [.term] O) (stable : Stable G) :
    Trace (Search.Step (before G)) (.search,.input 0) (.rewrite,.input 0) 3 := by
  let p : (before G).Vertex := .internal (.inl (0 : Fin 1))
  have first : Search.Step (before G) (.search,.input 0) (.search,p) := by
    cases d
    all_goals
      apply Search.Step.search (G := before G) ⟨false,(0 : Fin 1)⟩ (.operation (.unary .ref)) _ _ rfl
      · exact List.mem_cons_self
      · rfl
  have middle : Search.Step (before G) (.search,p) (.backtrack,p) := by
    obtain ⟨e,_⟩ := stable.exists_unique_edge
    obtain ⟨q,label,hq⟩ := stable.labels e
    cases d
    all_goals
      apply Search.Step.search (G := before G) ⟨true,e⟩ q _ _ label
      · exact List.mem_map_of_mem (Stable.input_source stable.labels e)
      · exact Search.enter_stable q hq _ _
  have last : Search.Step (before G) (.backtrack,p) (.rewrite,.input 0) := by
    cases d
    all_goals
      exact Search.Step.backtrack (G := before G) ⟨false,(0 : Fin 1)⟩ (.unary .ref) (.input 0) _ 0 _
        rfl rfl (by decide) rfl rfl
  exact .step first (.step middle (.step last (.refl _)))
end Allocation

namespace OperationalTemplates
/-- Exact search cost before the one original compute transition. -/
def Kind.searchCost : Kind → Nat
  | .microBeta => 5
  | .referenceCreation => 3

/-- These are original search rules; the beta body is not evaluated. -/
theorem Literal.entry_trace {kind d I O} {G H : Hypernet d I O}
    (pair : Literal kind G H) :
    ∃ i : Fin I.length,
      Trace (Search.Step G) (.search,.input i) (.rewrite,.input i) kind.searchCost := by
  cases pair with
  | beta B G free stable => exact ⟨0,Application.search_trace B G stable⟩
  | reference G stable => exact ⟨0,Allocation.entry_trace G stable⟩

/-- The finite entry prefix survives independent carrier names on either side. -/
theorem Pair.entry_prefix {kind d I O} {G H : Hypernet d I O}
    (pair : Pair kind G H) :
    ∃ i : Fin I.length,
      Trace (Search.Step G) (.search,.input i) (.rewrite,.input i) kind.searchCost ∧
      Rewrite G (.input i) H (.input i) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | beta B A free stable =>
      refine ⟨0,?_,.rename f.symm g (.local (.beta B A stable))⟩
      exact (Application.search_trace B A stable).map
        (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).positions.toFun
        (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step
    | reference A stable =>
      refine ⟨0,?_,.rename f.symm g (.local (.allocate A stable))⟩
      exact (Allocation.entry_trace A stable).map
        (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).positions.toFun
        (Search.ofBoundaryIso (BoundaryIso.ofDeepIso f.symm)).step

/-- Operational pairs have exactly one input, even after independent renaming. -/
theorem Pair.input {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    I = [.term] := by
  cases pair with | witness f pair g => exact pair.input

end OperationalTemplates

namespace OperationalSafety
/-- Change exactly one original component, retaining the dependent interfaces. -/
noncomputable def replace {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (b : C.Edge) := by
  classical
  exact if eq : b = e then eq.symm ▸ H else F b

@[simp] theorem replace_selected {d I O} (C : Hypernet d I O) (F) (e) (H) :
    replace C F e H e = H := by classical simp [replace]

theorem replace_other {d I O} (C : Hypernet d I O) (F) (e) (H) (b) (ne : b ≠ e) :
    replace C F e H b = F b := by classical simp [replace,ne]

/-- Consume the selected hole into the common context.  Other original edges
keep their assigned components; inserted edges are retained by corollas. -/
def remaining {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (x : (C.plug e H).Edge) :
    Hypernet d ((alphabet d).signature.input ((C.plug e H).edgeLabel x))
      ((alphabet d).signature.output ((C.plug e H).edgeLabel x)) :=
  match x with
  | .inl b => F b.val
  | .inr f => Net.corolla (alphabet d).signature (H.edgeLabel f)

/-- Peeling retains the exact original host token, not only an unpointed graph. -/
theorem remaining_iso {d I O} (C : Hypernet d I O) (F) (e) (H) :
    ∃ f : DeepIso ((C.plug e H).expand (remaining C F e H))
        (C.expand (replace C F e H)),
      ∀ v, Port.map f.vertices.toFun
        (Net.Expansion.host (C.plug e H) (remaining C F e H)
          (Net.Replacement.host C e H v)) =
        Net.Expansion.host C (replace C F e H) v := by
  classical
  let K := replace C F e H
  have aux (H') (eq : K e = H') :
      ∃ f : DeepIso ((C.plug e H').expand (remaining C F e H')) (C.expand K),
        ∀ v, Port.map f.vertices.toFun
          (Net.Expansion.host (C.plug e H') (remaining C F e H')
            (Net.Replacement.host C e H' v)) = Net.Expansion.host C K v := by
    subst H'
    have family : remaining C F e (K e) = Net.ExpansionPeel.rest C K e := by
      funext x
      cases x with
      | inl b => exact (replace_other C F e H b.val b.property).symm
      | inr x => rfl
    rw [family]
    exact ⟨DeepIso.ofIso (Net.ExpansionPeel.iso C K e),Net.ExpansionPeel.map_host C K e⟩
  exact aux H (replace_selected C F e H)

/-- Once a closed right-hand graph replaces the entered hole, the same host
coordinate cannot enter a remaining hole. Incidence uniqueness is essential. -/
theorem consumed_not_entering {d I O} (C : Hypernet d I O) (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (closed : HoleFree H)
    (i : Fin ((alphabet d).signature.input (C.edgeLabel e)).length) :
    ¬ Search.Expansion.Entering (C.plug e H)
      (.search,Net.Replacement.host C e H (C.sourcePort e i)) := by
  rintro ⟨f,h,label,mem⟩
  cases f with
  | inl f =>
    obtain ⟨v,src,eq⟩ := List.mem_map.mp mem
    have eq := Net.Replacement.host_injective C e H eq
    have edge := C.source_unique (eq ▸ src) (C.sourcePort_mem e i)
    exact f.property edge
  | inr f =>
    have bad := closed f
    change LabelAll (fun p => ∀ h, p ≠ .hole h) d (H.edgeLabel f) at bad
    change H.edgeLabel f = primitiveLabel d (.hole h) at label
    rw [label] at bad
    cases d <;> exact bad h rfl

/-- Every unconsumed edge keeps precisely its previous recursive certificate. -/
theorem remaining_edges {T d I O} (C : Hypernet d I O) (F K) (e) (H)
    (edges : ∀ b, DeepFillingEdge T C F K b) :
    ∀ x, DeepFillingEdge T (C.plug e H) (remaining C F e H) (remaining C K e H) x := by
  intro x
  cases x with
  | inl b =>
    cases d with
    | zero =>
      cases edges b.val with
      | retained l r => exact .retained l r
      | filled h label rel => exact .filled h label rel
    | succ d =>
      cases edges b.val with
      | retained l r => exact .retained l r
      | filled h label rel => exact .filled h label rel
      | boxed b label inner l r => exact .boxed b label inner l r
  | inr x => exact .retained (LabelCopy.corolla _) (LabelCopy.corolla _)

/-- An arbitrary finite search trace remains a trace of the full machine. -/
theorem search_run {d I O} (G : Hypernet d I O) {s t n}
    (run : Trace (Search.Step G) s t n) :
    (Combined.machine d I O).Steps n ⟨G,s⟩ ⟨G,t⟩ := by
  induction run with
  | refl => exact .zero _
  | step first rest ih => exact .cons (.search G first) ih

/-- Consume one original entered hole, retaining all unrelated shallow and deep
replacements.  The right graph moves into the shared context and the token is
settled there.  The endpoint equations are in the actual representation quotient. -/
theorem consume {kind Allowed} (S : Specimen (OperationalTemplates.template kind) Allowed)
    (e : S.context.Edge)
    (pair : OperationalTemplates.Pair kind (S.left e) (S.right e))
    (i : Fin ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length)
    (token : S.token = (.search,S.context.sourcePort e i))
    (allowed : Allowed S.depth (S.context.plug e (S.right e))) :
    ∃ D : Specimen (OperationalTemplates.template kind) Allowed,
      D.token.1 = .search ∧ ¬ D.Entering ∧
      StateClass.machine.Steps (kind.searchCost+1)
        (StateClass.ofState S.leftState) (StateClass.ofState D.leftState) ∧
      StateClass.ofState D.rightState = StateClass.ofState S.rightState := by
  classical
  let C := S.context
  let H := S.right e
  let K := replace C S.left e H
  have rightFree : FocusFree H := pair.focusFree.2
  have rightClosed : HoleFree H := fun x => S.right_closed ⟨e,x⟩
  obtain ⟨j,trace,rewrite⟩ := pair.entry_prefix
  have index : j = i := by
    have interface := pair.input
    apply Fin.ext
    have hj := j.isLt
    have hi := i.isLt
    have length : ((alphabet S.depth).signature.input (S.context.edgeLabel e)).length = 1 :=
      congrArg List.length interface
    change j.val = i.val
    omega
  subst j
  have selectedStep : Rewrite (C.expand S.left)
      (Net.Expansion.host C S.left (C.sourcePort e i)) (C.expand K)
      (Net.Expansion.host C K (C.sourcePort e i)) := by
    have aux (H') (eq : K e = H')
        (step : Rewrite (S.left e) (.input i) H' (.input i)) :
        Rewrite (C.expand S.left) (Net.Expansion.host C S.left (C.sourcePort e i))
          (C.expand K) (Net.Expansion.host C K (C.sourcePort e i)) := by
      subst H'
      exact .expand C S.left K e
        (fun b ne => (replace_other C S.left e H b ne).symm) step
    exact aux H (replace_selected C S.left e H) rewrite
  have closedK : HoleFree (C.expand K) := rewrite_holeFree selectedStep S.left_closed
  have run : (Combined.machine S.depth [.term] []).Steps (kind.searchCost+1)
      ⟨C.expand S.left,(.search,Net.Expansion.host C S.left (C.sourcePort e i))⟩
      ⟨C.expand K,(.search,Net.Expansion.host C K (C.sourcePort e i))⟩ := by
    have traversal := search_run (C.expand S.left)
      (trace.map (fun q => (q.1,Net.Expansion.insert C S.left e q.2))
        (Search.expand_insert C S.left e))
    exact traversal.append (.cons (.rewrite selectedStep) (.zero _))
  obtain ⟨leftIso,leftPoint⟩ := remaining_iso C S.left e H
  have rightData : ∃ f : DeepIso ((C.plug e H).expand (remaining C S.right e H))
      (C.expand S.right), ∀ v, Port.map f.vertices.toFun
      (Net.Expansion.host (C.plug e H) (remaining C S.right e H)
        (Net.Replacement.host C e H v)) = Net.Expansion.host C S.right v := by
    have family : remaining C S.right e H = Net.ExpansionPeel.rest C S.right e := by
      funext x; cases x <;> rfl
    rw [family]
    exact ⟨DeepIso.ofIso (Net.ExpansionPeel.iso C S.right e),
      Net.ExpansionPeel.map_host C S.right e⟩
  obtain ⟨rightIso,rightPoint⟩ := rightData
  let D : Specimen (OperationalTemplates.template kind) Allowed := {
    depth := S.depth
    context := C.plug e H
    allowed := allowed
    free := focusFree_closed (.shallow C e) H S.free rightFree
    left := remaining C S.left e H
    right := remaining C S.right e H
    edges := remaining_edges C S.left S.right e H S.edges
    left_closed := (allLabels_iso_iff _ leftIso).mpr closedK
    right_closed := (allLabels_iso_iff _ rightIso).mpr S.right_closed
    token := (.search,Net.Replacement.host C e H (C.sourcePort e i))
    term := by
      have typed := S.term
      rw [token] at typed
      change C.vertexLabel (C.sourcePort e i) = .term at typed
      have hostLabel (v : C.Vertex) :
          (C.plug e H).vertexLabel (Net.Replacement.host C e H v) = C.vertexLabel v := by
        cases v <;> rfl
      exact (hostLabel _).trans typed }
  have l : StateClass.ofState D.leftState =
      StateClass.ofState ⟨S.depth,C.expand K,
        (.search,Net.Expansion.host C K (C.sourcePort e i))⟩ :=
    Quotient.sound (.iso (.lift ⟨leftIso,rfl,leftPoint _⟩))
  have r : StateClass.ofState D.rightState =
      StateClass.ofState ⟨S.depth,C.expand S.right,
        (.search,Net.Expansion.host C S.right (C.sourcePort e i))⟩ :=
    Quotient.sound (.iso (.lift ⟨rightIso,rfl,rightPoint _⟩))
  refine ⟨D,rfl,consumed_not_entering C e H rightClosed i,?_,?_⟩
  · rw [l]
    have start : S.leftState = ⟨S.depth,C.expand S.left,
        (.search,Net.Expansion.host C S.left (C.sourcePort e i))⟩ := by
      simp only [Specimen.leftState,token,Search.Expansion.position,C]
    rw [start]
    exact StateClass.project_run (run_unbounded run)
  · have finish : S.rightState = ⟨S.depth,C.expand S.right,
        (.search,Net.Expansion.host C S.right (C.sourcePort e i))⟩ := by
      simp only [Specimen.rightState,token,Search.Expansion.position,C]
    rw [finish]
    exact r

/-- The only context-class obligation in the consumption argument is the
paper's sourced-hole plugging closure.  The inserted graph is proved closed. -/
theorem inputSafe_of_plugging (kind : OperationalTemplates.Kind)
    (Allowed : ∀ d, Hypernet d [.term] [] → Prop)
    (plugging : ∀ d (C : Hypernet d [.term] []), Allowed d C →
      ∀ (e : C.Edge), HoleLabel d (C.edgeLabel e) → (∃ v, v ∈ C.source e) →
      ∀ (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
        ((alphabet d).signature.output (C.edgeLabel e))),
        FocusFree H → HoleFree H → Allowed d (C.plug e H))
    (Q P : CostOrder) (cost : Q.rel (kind.searchCost+1) 0) :
    (Specimens.system (OperationalTemplates.template kind) Allowed
      (OperationalTemplates.template_outputClosed kind)).InputSafe Q P := by
  intro S _ _ mode entering
  change S.token.1 = .search at mode
  obtain ⟨e,h,label,mem⟩ := entering
  have pair := (S.edges e).relation_at_hole label S.left_closed
  obtain ⟨i,eq⟩ := (S.context.mem_source_iff_port e S.token.2).mp mem
  have token : S.token = (.search,S.context.sourcePort e i) := Prod.ext mode eq.symm
  have allowed := plugging S.depth S.context S.allowed e ⟨h,label⟩ ⟨_,mem⟩
    (S.right e) pair.focusFree.2 (fun x => S.right_closed ⟨e,x⟩)
  obtain ⟨D,search,away,run,right⟩ := consume S e pair i token allowed
  right; left
  refine ⟨D,kind.searchCost,0,Or.inr ⟨search,away⟩,?_,?_,?_⟩
  · simpa only [Nat.add_comm 1] using cost
  · change StateClass.machine.Steps (1+kind.searchCost)
      (StateClass.ofState S.leftState) (StateClass.ofState D.leftState)
    simpa only [Nat.add_comm 1] using run
  · change StateClass.machine.Steps 0 (StateClass.ofState S.rightState)
      (StateClass.ofState D.rightState)
    rw [right]
    exact .zero _
end OperationalSafety

namespace OperationalTemplates
/-- Full input safety for every original unrestricted context, retaining the
exact comparison between the 6/4-step prefix and the zero-step right run. -/
theorem template_inputSafe_cost (kind : Kind) (Q P : CostOrder)
    (cost : Q.rel (kind.searchCost+1) 0) :
    (Specimens.system (template kind) Specimens.allContexts
      (template_outputClosed kind)).InputSafe Q P :=
  OperationalSafety.inputSafe_of_plugging kind Specimens.allContexts
    (fun _ _ _ _ _ _ _ _ _ => trivial) Q P cost

/-- Full input safety in the paper's binding-free observation class. Sourced-hole
plugging closure is proved, and hole-freedom supplies binding-freedom of the
consumed right graph. No closure or stability hypothesis is left to applications. -/
theorem template_bindingFree_inputSafe_cost (kind : Kind) (Q P : CostOrder)
    (cost : Q.rel (kind.searchCost+1) 0) :
    (Specimens.system (template kind) Specimens.bindingFreeContexts
      (template_outputClosed kind)).InputSafe Q P := by
  apply OperationalSafety.inputSafe_of_plugging kind Specimens.bindingFreeContexts
    (Q := Q) (P := P) (cost := cost)
  intro d C free e hole source H hf hc
  exact BindingFree.plugAt (.shallow C e) H ⟨hole,source⟩ free
    (BindingFree.of_holeFree H hf hc)

/-- Both operational families are input-safe for termination observation, with
any equivalence-up-to cost parameter; the proof uses settled case II throughout. -/
theorem template_inputSafe (kind : Kind) (P : CostOrder) :
    (Specimens.system (template kind) Specimens.allContexts
      (template_outputClosed kind)).InputSafe CostOrder.any P :=
  template_inputSafe_cost kind CostOrder.any P trivial

/-- The input-safety premise needed for Proposition 12.2's actual observation class. -/
theorem template_bindingFree_inputSafe (kind : Kind) (P : CostOrder) :
    (Specimens.system (template kind) Specimens.bindingFreeContexts
      (template_outputClosed kind)).InputSafe CostOrder.any P :=
  template_bindingFree_inputSafe_cost kind CostOrder.any P trivial

/-- The forward direction also preserves the paper's non-increasing-cost
comparison before costs are forgotten for termination equivalence. -/
theorem template_bindingFree_inputSafe_improvement (kind : Kind) (P : CostOrder) :
    (Specimens.system (template kind) Specimens.bindingFreeContexts
      (template_outputClosed kind)).InputSafe CostOrder.improvement P :=
  template_bindingFree_inputSafe_cost kind CostOrder.improvement P (Nat.zero_le _)
end OperationalTemplates
end Hypernets.Copying

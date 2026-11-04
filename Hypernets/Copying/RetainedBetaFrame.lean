import Hypernets.Copying.ApplicationCoherence
import Hypernets.Copying.CompleteMatchRewrite
import Hypernets.Copying.LocalRewriteOccurrence
import Hypernets.Copying.ConverseArgumentHistory

/-! The exact app/lambda/box frame, exposing the argument wire instead of
including any stable argument edge. It is proof geometry, not a new rule. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application.RetainedFrame
open Graph Opening
inductive Edge where
  | app | lam | box
  deriving DecidableEq

@[simp] theorem edge_exists (P : Edge → Prop) : (∃ e, P e) ↔ P .app ∨ P .lam ∨ P .box := by
  constructor
  · rintro ⟨e,p⟩; cases e <;> simp_all
  · rintro (p | p | p)
    · exact ⟨.app,p⟩
    · exact ⟨.lam,p⟩
    · exact ⟨.box,p⟩

@[simp] theorem edge_forall (P : Edge → Prop) : (∀ e, P e) ↔ P .app ∧ P .lam ∧ P .box := by
  constructor
  · intro p; exact ⟨p _,p _,p _⟩
  · intro p e; cases e
    · exact p.1
    · exact p.2.1
    · exact p.2.2
variable {d k h} (B : Hypernet d [.term] (environmentInterface (k+1) h))
abbrev Vertex := Port Bool 1 (.term :: environmentInterface k h).length

def freePort (i : Fin (environmentInterface k h).length) : Vertex (k := k) (h := h) := .output i.succ
def freePorts : List (Vertex (k := k) (h := h)) := (List.finRange (environmentInterface k h).length).map freePort

def label : Edge → (alphabet (d+1)).Symbol
  | .app => primitiveLabel (d+1) (.operation .app)
  | .lam => primitiveLabel (d+1) (.operation .lam)
  | .box => .inr ⟨1,k,h,Translation.castInterfaces rfl (by rw [Nat.add_comm k 1]) B⟩

def source : Edge → List (Vertex (k := k) (h := h))
  | .app => [.input 0]
  | .lam => [.internal false]
  | .box => [.internal true]
def target : Edge → List (Vertex (k := k) (h := h))
  | .app => [.internal false,.output 0]
  | .lam => [.internal true]
  | .box => freePorts

theorem freePort_injective : Function.Injective (freePort (k := k) (h := h)) := by
  intro i j eq
  exact Fin.ext (Nat.succ.inj (congrArg Fin.val (Port.output.inj eq)))

def net : Hypernet (d+1) [.term] (.term :: environmentInterface k h) where
  Internal := Bool
  Edge := Edge
  finiteInternal := ⟨[false,true],by intro b; cases b <;> simp⟩
  finiteEdge := ⟨[.app,.lam,.box],by intro e; cases e <;> simp⟩
  internalLabel b := if b then .thunk 1 else .term
  edgeLabel := label B
  source := source
  target := target
  source_nodup e := by cases e <;> simp [source]
  target_nodup e := by
    cases e <;> simp only [target]
    · simp
    · simp
    · exact nodup_map_on (finRange_nodup _) (fun i j _ _ eq => freePort_injective eq)
  source_unique := by intro v a b ha hb; cases a <;> cases b <;> simp_all [source]
  target_unique := by
    intro v a b ha hb
    cases a <;> cases b <;> simp_all [target,freePorts,freePort]
    · obtain ⟨i,rfl⟩ := hb
      rcases ha with eq | eq
      · cases eq
      · have bad := congrArg Fin.val (Port.output.inj eq); simp at bad
    · obtain ⟨i,rfl⟩ := ha
      rcases hb with eq | eq
      · cases eq
      · have bad := congrArg Fin.val (Port.output.inj eq); simp at bad
  source_coverage := by
    intro v
    cases v with
    | internal b => cases b <;> simp [source,Port.IsOutput,edge_exists]
    | input i => change Fin 1 at i; have eq : i = 0 := Subsingleton.elim _ _; subst i; simp [source,Port.IsOutput,edge_exists]
    | output i => simp [source,Port.IsOutput,edge_exists]
  target_coverage := by
    intro v
    cases v with
    | internal b => cases b <;> simp [target,freePorts,freePort,Port.IsInput,edge_exists]
    | input i => simp [target,freePorts,freePort,Port.IsInput,edge_exists]
    | output i =>
      cases i using Fin.cases with
      | zero => simp [target,Port.IsInput,edge_exists]
      | succ i =>
        constructor
        · intro _; simp [Port.IsInput]
        · intro _
          exact ⟨.box,List.mem_map.mpr ⟨i,List.mem_finRange i,rfl⟩⟩
  source_typed e := by cases e <;> rfl
  target_typed e := by
    cases e <;> simp only [target,label]
    · rfl
    · rfl
    · change (freePorts (k := k) (h := h)).map (Port.label (I := [Wire.term]) (O := Wire.term :: environmentInterface k h) (fun b : Bool => if b then Wire.thunk 1 else Wire.term)) = environmentInterface k h
      simp [freePorts,freePort,Port.label,Function.comp_def,
        List.finRange,List.map_ofFn,List.ofFn_getElem]

section Occurrence
variable {I O} {G : Hypernet (d+1) I O} {v : G.Vertex} (a : Match G v B)

def ports : (net B).Vertex → G.Vertex
  | .input _ => v
  | .internal false => .internal a.functionWire
  | .internal true => .internal a.thunkWire
  | .output i => (a.argumentPort :: G.target a.boxEdge)[i.val]'(by rw [a.output_length]; exact i.isLt)

def edges : (net B).Edge → G.Edge
  | .app => a.app
  | .lam => a.lam
  | .box => a.boxEdge

theorem edges_injective : Function.Injective (edges B a) := by
  intro e f eq
  have headLam : a.app ≠ a.lam := by
    intro same
    have bad := a.head_at.1
    rw [same,a.lambda_label] at bad
    cases bad
  have headBox : a.app ≠ a.boxEdge := by
    intro same
    have rel := a.box_label
    rw [← same,a.head_at.1] at rel
    exact rel
  have lamBox : a.lam ≠ a.boxEdge := by
    intro same
    have rel := a.box_label
    rw [← same,a.lambda_label] at rel
    exact rel
  cases e <;> cases f <;> first | rfl | exact False.elim (headLam eq) | exact False.elim (headLam eq.symm) | exact False.elim (headBox eq) | exact False.elim (headBox eq.symm) | exact False.elim (lamBox eq) | exact False.elim (lamBox eq.symm)

theorem ports_free : freePorts.map (ports B a) = G.target a.boxEdge := by
  have len : (G.target a.boxEdge).length = (environmentInterface k h).length := by
    have eq := a.output_length
    exact Nat.succ.inj eq
  change ((List.finRange (environmentInterface k h).length).map freePort).map (ports B a) = _
  simp only [List.map_map]
  change (List.finRange (environmentInterface k h).length).map (fun i => (G.target a.boxEdge)[i.val]'_) = _
  apply List.ext_getElem
  · simpa using len.symm
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_finRange]
    rfl

def embedding : MatchEmbedding (net B) G where
  ports := ports B a
  edges := edges B a
  edge_injective := edges_injective B a
  primitive e p eq := by
    cases e
    · have same := primitiveLabel_injective (d+1) eq
      subst p; exact a.head_at.1
    · have same := primitiveLabel_injective (d+1) eq
      subst p; exact a.lambda_label
    · cases eq
  source e := by
    cases e
    · exact (Search.operation_source a.head_at.1 a.head_at.2).symm
    · exact a.lambda_source.symm
    · exact a.box_source.symm
  target e := by
    cases e
    · exact a.app_target.symm
    · exact a.lambda_target.symm
    · exact ports_free B a

/-- The full original opening match supplies a complete occurrence of only
its app/lambda/box frame. The entire argument lies outside this footprint. -/
noncomputable def occurrence : Occurrence (net B) G :=
  (embedding B a).occurrence (fun e => by
    cases e
    · change LabelEquiv (d+1) (primitiveLabel (d+1) (.operation .app)) (G.edgeLabel a.app)
      rw [a.head_at.1]; exact labelEquiv_refl _ _
    · change LabelEquiv (d+1) (primitiveLabel (d+1) (.operation .lam)) (G.edgeLabel a.lam)
      rw [a.lambda_label]; exact labelEquiv_refl _ _
    · exact labelEquiv_symm _ a.box_label)

theorem occurrence_input : (occurrence B a).ports (.input 0) = v := rfl

theorem occurrence_argument : (occurrence B a).ports (.output 0) = a.argumentPort := rfl

end Occurrence

end Hypernets.Copying.Application.RetainedFrame

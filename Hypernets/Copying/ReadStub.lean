import Hypernets.Copying.AssignmentCoherenceExamples

/-! A proof-side read graft. Its temporary feedback wire is reconnected to the existing
store before comparison with the original rule. It introduces no machine transition. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ReadStub
open Graph

theorem fin_four (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega

/-- One consumed-instance weakening and the three literal edges of D-term-1-2. -/
def label (i : Fin 4) : Primitive :=
  if i.val < 2 then .weakening .term else .contraction .term

def source (i : Fin 4) : List (Port (Fin 3) 1 1) :=
  if i.val < 2 then [] else if i.val = 2 then [.internal 1,.internal 2]
  else [.internal 0,.input 0]

def target (i : Fin 4) : List (Port (Fin 3) 1 1) :=
  if i.val = 0 then [.output 0] else if i.val = 1 then [.internal 1]
  else if i.val = 2 then [.internal 0] else [.internal 2]

/-- The temporary feedback joins the distributor's first input to its output. -/
def base : Net primitiveSignature [.term] [.term] where
  Internal := Fin 3
  Edge := Fin 4
  finiteInternal := Enumeration.fin 3
  finiteEdge := Enumeration.fin 4
  internalLabel _ := .term
  edgeLabel := label
  source := source
  target := target
  source_nodup e := by rcases fin_four e with rfl | rfl | rfl | rfl <;> simp +decide
  target_nodup e := by rcases fin_four e with rfl | rfl | rfl | rfl <;> simp +decide
  source_unique := by
    intro v e f he hf
    rcases fin_four e with rfl | rfl | rfl | rfl <;>
      rcases fin_four f with rfl | rfl | rfl | rfl <;> simp_all +decide [source]
    all_goals rcases he with rfl | rfl <;> simp_all
  target_unique := by
    intro v e f he hf
    rcases fin_four e with rfl | rfl | rfl | rfl <;>
      rcases fin_four f with rfl | rfl | rfl | rfl <;> simp_all +decide [target]
  source_coverage := by
    intro v
    cases v with
    | internal i =>
      rcases DiscardResult.fin_three i with rfl | rfl | rfl
      · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨3,by simp +decide⟩⟩
      · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨2,by simp +decide⟩⟩
      · exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨2,by simp +decide⟩⟩
    | input i =>
      cases DiscardResult.fin_one i
      exact ⟨fun _ => by simp [Port.IsOutput],fun _ => ⟨3,by simp +decide⟩⟩
    | output i =>
      cases DiscardResult.fin_one i
      simp only [Port.IsOutput,not_true_eq_false,iff_false,not_exists]
      intro e; rcases fin_four e with rfl | rfl | rfl | rfl <;> simp +decide
  target_coverage := by
    intro v
    cases v with
    | internal i =>
      rcases DiscardResult.fin_three i with rfl | rfl | rfl
      · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨2,by simp +decide⟩⟩
      · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨1,by simp +decide⟩⟩
      · exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨3,by simp +decide⟩⟩
    | input i =>
      cases DiscardResult.fin_one i
      simp only [Port.IsInput,not_true_eq_false,iff_false,not_exists]
      intro e; rcases fin_four e with rfl | rfl | rfl | rfl <;> simp +decide
    | output i =>
      cases DiscardResult.fin_one i
      exact ⟨fun _ => by simp [Port.IsInput],fun _ => ⟨0,by simp +decide⟩⟩
  source_typed e := by rcases fin_four e with rfl | rfl | rfl | rfl <;> rfl
  target_typed e := by rcases fin_four e with rfl | rfl | rfl | rfl <;> rfl

def net (d : Nat) : Hypernet d [.term] [.term] :=
  base.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)
end Hypernets.Copying.ReadStub

import Hypernets.Copying.ContractionTreeGraftFrame
import Hypernets.Copying.CopyPayloadRigidity
import Hypernets.Copying.SharingTreeResiduals

/-! Graft an arbitrary upstream graph into one ordered sharing input of an
arbitrary downstream graph. The contraction-tree specialization includes
zero-input residual trees and retains literal component ownership. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph Opening
variable {s : ShareSort} {a b d : Nat} {O : List Wire}

def pattern (s : ShareSort) (a b : Nat) (O : List Wire) (j : Fin (b+1)) (d : Nat) :
    Hypernet d (List.replicate (a+b) s.wire) O :=
  (frame s a b O j).relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)

def filling (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) O) (j : Fin (b+1))
    (e : (pattern s a b O j d).Edge) :
    Hypernet d ((alphabet d).signature.input ((pattern s a b O j d).edgeLabel e))
      ((alphabet d).signature.output ((pattern s a b O j d).edgeLabel e)) := by
  cases d <;> cases e
  all_goals first | exact P | exact G

/-- Literal partial serial composition, retaining every unselected input in
its original relative order after all upstream inputs. -/
def net (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) O) (j : Fin (b+1)) :
    Hypernet d (List.replicate (a+b) s.wire) O :=
  (pattern s a b O j d).expand (filling P G j)

variable (P : Hypernet d (List.replicate a s.wire) [s.wire])
    (G : Hypernet d (List.replicate (b+1) s.wire) O) (j : Fin (b+1))

def leftInsert : P.Vertex → (net P G j).Vertex := by
  cases d <;> exact Net.Expansion.insert (pattern s a b O j _) (filling P G j) false

def rightInsert : G.Vertex → (net P G j).Vertex := by
  cases d <;> exact Net.Expansion.insert (pattern s a b O j _) (filling P G j) true

noncomputable def leftOccurrence : Occurrence P (net P G j) := by
  cases d <;> exact Occurrence.expand (pattern s a b O j _) (filling P G j) false

noncomputable def rightOccurrence : Occurrence G (net P G j) := by
  cases d <;> exact Occurrence.expand (pattern s a b O j _) (filling P G j) true

theorem leftOccurrence_ports (v : P.Vertex) : (leftOccurrence P G j).ports v = leftInsert P G j v := by
  cases d <;> rfl

theorem rightOccurrence_ports (v : G.Vertex) : (rightOccurrence P G j).ports v = rightInsert P G j v := by
  cases d <;> rfl

theorem left_input (i : Fin (List.replicate a s.wire).length) :
    leftInsert P G j (.input i) = .input ⟨i.val,by have := i.isLt; simp only [List.length_replicate] at *; omega⟩ := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern s a b O j _).sourcePort false _) = _
    simp only [Net.sourcePort,pattern,frame,sources,Net.relabel,List.getElem_map,
      List.getElem_finRange,upstream,Port.map,Fin.val_cast]

theorem right_output (i : Fin O.length) : rightInsert P G j (.output i) = .output i := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern s a b O j _).targetPort true _) = _
    simp only [Net.targetPort,pattern,frame,targets,Net.relabel,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

theorem right_input (i : Fin (List.replicate (b+1) s.wire).length) :
    rightInsert P G j (.input i) = Port.map Sum.inl (downstream s a b O j ⟨i.val,by simpa using i.isLt⟩) := by
  cases d
  all_goals
    change Port.map Sum.inl ((pattern s a b O j _).sourcePort true _) = _
    simp only [Net.sourcePort,pattern,frame,sources,Net.relabel,List.getElem_map,List.getElem_finRange,Fin.cast_mk]

/-- The selected downstream input is exactly the actual upstream root. -/
theorem selected_input :
    rightInsert P G j (.input ⟨j.val,by simp⟩) = leftInsert P G j (.output 0) := by
  have root : leftInsert P G j (.output 0) = Port.internal (.inl (0 : Fin 1)) := by
    cases d <;> rfl
  rw [root,right_input]
  change Port.map Sum.inl (downstream s a b O j j) = _
  rw [downstream_selected]
  rfl

end Hypernets.Copying.ContractionTree.Graft

namespace Hypernets.Copying.ContractionTree
open Graph
variable {s : ShareSort} {a b : Nat}

def Graft.treeFilling (P : ContractionTree s a) (T : ContractionTree s (b+1))
    (e : Bool) : Net primitiveSignature
      (primitiveSignature.input (Graft.label s a b [s.wire] e))
      (primitiveSignature.output (Graft.label s a b [s.wire] e)) := by
  cases e
  · exact P.net
  · exact T.net

/-- Insert the complete upstream tree into precisely one downstream input.
The case a=0 includes actual weakened residual trees. -/
def graftInput (P : ContractionTree s a) (T : ContractionTree s (b+1)) (j : Fin (b+1)) :
    ContractionTree s (a+b) where
  net := (Graft.frame s a b [s.wire] j).expand (Graft.treeFilling P T)
  labels e := by
    rcases e with ⟨side,e⟩
    cases side
    · exact P.labels e
    · exact T.labels e
  acyclic := by
    apply SharingTreeExpansion.acyclic_expand _ _ (Graft.frame_acyclic s a b [s.wire] j)
    · intro e; cases e <;> rfl
    · intro e es path; cases e
      · exact P.acyclic path
      · exact T.acyclic path
    · intro e f; cases e
      · exact P.target_single f
      · exact T.target_single f

/-- Raising the literal primitive graft is the same original graph as grafting
its two raised components, with the same finite carriers and boundary ports. -/
def graftInput_iso (P : ContractionTree s a) (T : ContractionTree s (b+1))
    (j : Fin (b+1)) (d : Nat) :
    DeepIso ((graftInput P T j).atDepth d) (Graft.net (P.atDepth d) (T.atDepth d) j) := by
  have original := (FillingWitness.primitiveExpansionIso (Graft.frame s a b [s.wire] j)
    (Graft.treeFilling P T) d).symm
  have same : Graft.net (P.atDepth d) (T.atDepth d) j =
      (FillingWitness.liftedFrame (Graft.frame s a b [s.wire] j) d).expand
        (FillingWitness.liftedFamily (Graft.frame s a b [s.wire] j) (Graft.treeFilling P T) d) := by
    cases d
    all_goals
      apply congrArg ((Graft.pattern s a b [s.wire] j _).expand)
      funext e
      cases e <;> rfl
  rw [same]
  exact original

end Hypernets.Copying.ContractionTree

import Hypernets.Copying.OccurrenceInterfaceTransport

/-! Ordered tensor assembly of complete occurrences with independent interfaces. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Opening.Occurrence
open Graph

def tensorComponent {d I O J K} (G : Hypernet d I O) (H : Hypernet d J K) (b : Bool) :
    Occurrence (Net.Tensor.family G H b) (Net.Tensor.net G H) :=
  ParallelJoin.component _ (Net.Tensor.boundary I O J K) _ b

noncomputable def tensorMap {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') : Occurrence (Net.Tensor.net G H) (Net.Tensor.net G' H') :=
  ParallelJoin.occurrence _ (Net.Tensor.boundary I O J K) _
    (fun b => match b with
      | false => f.comp (tensorComponent G' H' false)
      | true => g.comp (tensorComponent G' H' true))
    (by intro a b ne e c eq; cases a <;> cases b
        · exact ne rfl
        · cases eq
        · cases eq
        · exact ne rfl)

theorem tensorMap_left {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (v : G.Vertex) :
    (tensorMap f g).ports ((tensorComponent G H false).ports v) =
      (tensorComponent G' H' false).ports (f.ports v) :=
  by
  unfold tensorMap tensorComponent
  exact ParallelJoin.occurrence_embed (Net.Tensor.family G H) (Net.Tensor.boundary I O J K) _ _ _ false v

theorem tensorMap_right {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (v : H.Vertex) :
    (tensorMap f g).ports ((tensorComponent G H true).ports v) =
      (tensorComponent G' H' true).ports (g.ports v) :=
  by
  unfold tensorMap tensorComponent
  exact ParallelJoin.occurrence_embed (Net.Tensor.family G H) (Net.Tensor.boundary I O J K) _ _ _ true v

theorem tensorMap_input_left {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (a : Fin I.length) (b : Fin U.length)
    (eq : f.ports (.input a) = .input b) :
    (tensorMap f g).ports (.input (Net.Tensor.join I J ⟨false,a⟩)) =
      .input (Net.Tensor.join U W ⟨false,b⟩) := by
  have law := tensorMap_left f g (.input a)
  rw [eq] at law
  exact law

theorem tensorMap_input_right {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (a : Fin J.length) (b : Fin W.length)
    (eq : g.ports (.input a) = .input b) :
    (tensorMap f g).ports (.input (Net.Tensor.join I J ⟨true,a⟩)) =
      .input (Net.Tensor.join U W ⟨true,b⟩) := by
  have law := tensorMap_right f g (.input a)
  rw [eq] at law
  exact law

theorem tensorMap_output_left {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (a : Fin O.length) (b : Fin V.length)
    (eq : f.ports (.output a) = .output b) :
    (tensorMap f g).ports (.output (Net.Tensor.join O K ⟨false,a⟩)) =
      .output (Net.Tensor.join V X ⟨false,b⟩) := by
  have law := tensorMap_left f g (.output a)
  rw [eq] at law
  exact law

theorem tensorMap_output_right {d I O J K U V W X}
    {G : Hypernet d I O} {H : Hypernet d J K} {G' : Hypernet d U V} {H' : Hypernet d W X}
    (f : Occurrence G G') (g : Occurrence H H') (a : Fin K.length) (b : Fin X.length)
    (eq : g.ports (.output a) = .output b) :
    (tensorMap f g).ports (.output (Net.Tensor.join O K ⟨true,a⟩)) =
      .output (Net.Tensor.join V X ⟨true,b⟩) := by
  have law := tensorMap_right f g (.output a)
  rw [eq] at law
  exact law

/-- An unchanged serial prefix is retained when the suffix's inputs stay fixed. -/
noncomputable def serialPrefix {d I J O K} (P : Hypernet d I J)
    {G : Hypernet d J O} {H : Hypernet d J K} (f : Occurrence G H)
    (inputs : ∀ i, f.ports (.input i) = .input i) :
    Occurrence (Serial.net P G) (Serial.net P H) :=
  SerialJoin.occurrence (BoxPullWeakening.RetainedCopy.serialLeftOccurrence P H)
    (f.comp (serialRight P H))
    (by intro i; change BoundarySerial.leftInsert P H (.output i) = BoundarySerial.rightInsert P H (f.ports (.input i))
        rw [inputs,CopyRule.serial_left_output,CopyRule.serial_right_input])
    (by cases d <;> intro e c eq <;> cases eq)

theorem serialPrefix_input {d I J O K} (P : Hypernet d I J)
    {G : Hypernet d J O} {H : Hypernet d J K} (f : Occurrence G H)
    (inputs : ∀ i, f.ports (.input i) = .input i) (i : Fin I.length) :
    (serialPrefix P f inputs).ports (.input i) = .input i := by
  unfold serialPrefix
  rw [SerialJoin.occurrence_input]
  exact Combined.left_input _ _ _

theorem serialPrefix_output {d I J O K} (P : Hypernet d I J)
    {G : Hypernet d J O} {H : Hypernet d J K} (f : Occurrence G H)
    (inputs : ∀ i, f.ports (.input i) = .input i) (a : Fin O.length) (b : Fin K.length)
    (out : f.ports (.output a) = .output b) :
    (serialPrefix P f inputs).ports (.output a) = .output b := by
  unfold serialPrefix
  rw [SerialJoin.occurrence_output]
  change BoundarySerial.rightInsert P H (f.ports (.output a)) = _
  rw [out,Application.right_serial_output]
end Hypernets.Copying.Opening.Occurrence

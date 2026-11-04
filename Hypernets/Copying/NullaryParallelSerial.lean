import Hypernets.Copying.BoundarySerial
import Hypernets.Copying.FillingAssembly

/-! Distribute serial composition over an ordered finite family whose first
components have no inputs. This exposes the exact distributor rows without
changing the resource permutation or deleting any graph component. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.NullaryParallelSerial
open Graph
variable {d : Nat} {A : Type} {J O : A → List Wire} {U V : List Wire}
    (F : ∀ a, Hypernet d [] (J a)) (G : ∀ a, Hypernet d (J a) (O a))
    (B : Net.Parallel.Boundary J O U V) (finite : Enumeration A)

/-- The input-free prefix forest uses precisely the suffix forest's input order. -/
def beforeBoundary : Net.Parallel.Boundary (fun _ : A => []) J [] U where
  inputs := ⟨fun x => Fin.elim0 x.2,fun i => Fin.elim0 i,
    fun x => Fin.elim0 x.2,fun i => Fin.elim0 i⟩
  outputs := B.inputs
  input_label _a i := Fin.elim0 i
  output_label := B.input_label

/-- The componentwise composite retains precisely the original output order. -/
def afterBoundary : Net.Parallel.Boundary (fun _ : A => []) O [] V where
  inputs := ⟨fun x => Fin.elim0 x.2,fun i => Fin.elim0 i,
    fun x => Fin.elim0 x.2,fun i => Fin.elim0 i⟩
  outputs := B.outputs
  input_label _a i := Fin.elim0 i
  output_label := B.output_label

abbrev left := Serial.net (Net.Parallel.net F (beforeBoundary B) finite) (Net.Parallel.net G B finite)
abbrev right := Net.Parallel.net (fun a => Serial.net (F a) (G a)) (afterBoundary B) finite

private def vertices : Bijection (left F G B finite).Internal (right F G B finite).Internal := by
  cases d
  all_goals exact {
    toFun := fun
      | .inl j => ⟨(B.inputs.invFun j).1,.inl (B.inputs.invFun j).2⟩
      | .inr ⟨false,⟨a,v⟩⟩ => ⟨a,.inr ⟨false,v⟩⟩
      | .inr ⟨true,⟨a,v⟩⟩ => ⟨a,.inr ⟨true,v⟩⟩
    invFun := fun
      | ⟨a,.inl j⟩ => .inl (B.inputs.toFun ⟨a,j⟩)
      | ⟨a,.inr ⟨false,v⟩⟩ => .inr ⟨false,⟨a,v⟩⟩
      | ⟨a,.inr ⟨true,v⟩⟩ => .inr ⟨true,⟨a,v⟩⟩
    left_inv := by
      rintro (j | ⟨b,v⟩)
      · exact congrArg Sum.inl (B.inputs.right_inv j)
      · cases b <;> rcases v with ⟨a,v⟩ <;> rfl
    right_inv := by
      rintro ⟨a,j | ⟨b,v⟩⟩
      · change (fun p : Σ a, Fin (J a).length => (⟨p.1,Sum.inl p.2⟩ : (right F G B finite).Internal))
          (B.inputs.invFun (B.inputs.toFun ⟨a,j⟩)) = _
        rw [B.inputs.left_inv]
      · cases b <;> rfl }

private def edges : Bijection (left F G B finite).Edge (right F G B finite).Edge := by
  cases d
  all_goals exact {
    toFun := fun | ⟨false,a,e⟩ => ⟨a,⟨false,e⟩⟩ | ⟨true,a,e⟩ => ⟨a,⟨true,e⟩⟩
    invFun := fun | ⟨a,⟨false,e⟩⟩ => ⟨false,a,e⟩ | ⟨a,⟨true,e⟩⟩ => ⟨true,a,e⟩
    left_inv := by rintro ⟨b,e⟩; cases b <;> rcases e with ⟨a,e⟩ <;> rfl
    right_inv := by rintro ⟨a,b,e⟩; cases b <;> rfl }

private theorem leftOutput {r I J O} (P : Hypernet r I J) (Q : Hypernet r J O)
    (j : Fin J.length) : BoundarySerial.leftInsert P Q (.output j) = .internal (.inl j) := by
  cases r
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort false j) = _
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

private theorem rightInput {r I J O} (P : Hypernet r I J) (Q : Hypernet r J O)
    (j : Fin J.length) : BoundarySerial.rightInsert P Q (.input j) = .internal (.inl j) := by
  cases r
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).sourcePort true j) = _
    simp only [Net.sourcePort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

private theorem rightOutput {r I J O} (P : Hypernet r I J) (Q : Hypernet r J O)
    (j : Fin O.length) : BoundarySerial.rightInsert P Q (.output j) = .output j := by
  cases r
  all_goals
    change Port.map Sum.inl ((Serial.pattern 0 I J O).targetPort true j) = _
    simp only [Net.targetPort,Serial.pattern,List.getElem_map,List.getElem_finRange,Port.map,Fin.cast_mk]

private theorem prefix_commutes (a : A) (v : (F a).Vertex) :
    Port.map (vertices F G B finite).toFun
      (BoundarySerial.leftInsert _ _ (Net.Parallel.embed F (beforeBoundary B) a v)) =
    Net.Parallel.embed (fun a => Serial.net (F a) (G a)) (afterBoundary B) a
      (BoundarySerial.leftInsert (F a) (G a) v) := by
  cases v with
  | input i => exact Fin.elim0 i
  | internal v => cases d <;> rfl
  | output i =>
    simp only [Net.Parallel.embed,beforeBoundary]
    rw [leftOutput,leftOutput]
    cases d
    all_goals
      change Port.internal
        ((fun p : Σ a, Fin (J a).length =>
          (⟨p.1,Sum.inl p.2⟩ : (right F G B finite).Internal))
          (B.inputs.invFun (B.inputs.toFun ⟨a,i⟩))) = _
      rw [B.inputs.left_inv]

private theorem suffix (a : A) (v : (G a).Vertex) :
    Port.map (vertices F G B finite).toFun
      (BoundarySerial.rightInsert _ _ (Net.Parallel.embed G B a v)) =
    Net.Parallel.embed (fun a => Serial.net (F a) (G a)) (afterBoundary B) a
      (BoundarySerial.rightInsert (F a) (G a) v) := by
  cases v with
  | internal v => cases d <;> rfl
  | input i =>
    simp only [Net.Parallel.embed]
    rw [rightInput,rightInput]
    cases d
    all_goals
      change Port.internal
        ((fun p : Σ a, Fin (J a).length =>
          (⟨p.1,Sum.inl p.2⟩ : (right F G B finite).Internal))
          (B.inputs.invFun (B.inputs.toFun ⟨a,i⟩))) = _
      rw [B.inputs.left_inv]
  | output i =>
    simp only [Net.Parallel.embed]
    rw [rightOutput,rightOutput]
    rfl

/-- Every shared wire and every original component edge is accounted for.
The theorem permits empty forests, arbitrary finite carriers and mixed sorts. -/
def iso : DeepIso (left F G B finite) (right F G B finite) where
  vertices := vertices F G B finite
  edges := edges F G B finite
  internal_label v := by
    cases d <;> rcases v with j | ⟨b,v⟩
    all_goals try (cases b <;> rcases v with ⟨a,v⟩ <;> rfl)
    all_goals
      change (J (B.inputs.invFun j).1)[(B.inputs.invFun j).2] = U[j]
      have law := B.input_label (B.inputs.invFun j).1 (B.inputs.invFun j).2
      change U[B.inputs.toFun (B.inputs.invFun j)] = _ at law
      simpa only [B.inputs.right_inv] using law.symm
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b <;> rcases e with ⟨a,e⟩ <;> exact labelEquiv_refl _ _
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b <;> rcases e with ⟨a,e⟩
    all_goals first
      | (change ((((F a).source e).map _).map _).map _ = (((F a).source e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => prefix_commutes F G B finite a v))
      | (change ((((G a).source e).map _).map _).map _ = (((G a).source e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => suffix F G B finite a v))
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b <;> rcases e with ⟨a,e⟩
    all_goals first
      | (change ((((F a).target e).map _).map _).map _ = (((F a).target e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => prefix_commutes F G B finite a v))
      | (change ((((G a).target e).map _).map _).map _ = (((G a).target e).map _).map _
         simp only [List.map_map]
         exact List.map_congr_left (fun v _ => suffix F G B finite a v))

end Hypernets.Copying.NullaryParallelSerial

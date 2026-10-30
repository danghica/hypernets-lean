import Hypernets.Copying.CopyingDoubleSource

/-! Exchanging the two active payload slots in the explicit common frame.
The actual row input permutation and outer input compensation are both retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.CopyingDouble.Symmetry
open Graph Opening

/-- Original input reindexing gives a complete ordered occurrence. -/
def forward {d I O} (G : Hypernet d I O) (p : TypedPermutation I) :
    Occurrence G (CopyingInputPermutation.net G p) where
  ports := (CopyingInputPermutation.ports G p).toFun
  internals := id
  edges := id
  internal_map _ := rfl
  internal_injective := fun _ _ h => h
  edge_injective := fun _ _ h => h
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source _ := rfl
  target _ := rfl

/-- Reverse the same actual ordered input action. -/
def backward {d I O} (G : Hypernet d I O) (p : TypedPermutation I) :
    Occurrence (CopyingInputPermutation.net G p) G where
  ports := (CopyingInputPermutation.ports G p).invFun
  internals := id
  edges := id
  internal_map _ := rfl
  internal_injective := fun _ _ h => h
  edge_injective := fun _ _ h => h
  internal_label _ := rfl
  label _ := labelEquiv_refl _ _
  source e := by
    change ((G.source e).map _).map _ = _
    rw [List.map_map]
    exact List.map_id'' (CopyingInputPermutation.ports G p).left_inv _
  target e := by
    change ((G.target e).map _).map _ = _
    rw [List.map_map]
    exact List.map_id'' (CopyingInputPermutation.ports G p).left_inv _

def swap (b : Fin 3) : Fin 3 := CopyingInputPermutation.exchange 0 1 b

theorem swap_swap (b : Fin 3) : swap (swap b) = b :=
  CopyingInputPermutation.exchange_involutive 0 1 b

theorem swap_injective : Function.Injective swap := by
  intro a b eq
  have := congrArg swap eq
  simpa only [swap_swap] using this

variable {d n k h}

def rowBack (i : Frame.Resource k h) : Occurrence (Frame.row (d := d) i true) (Frame.row i false) :=
  BoxPullWeakening.RetainedCopy.targetCast
    ((backward (Row.graph (Frame.sort k h i) d) (Row.exchange (Frame.sort k h i))).reboundarySource
      (congrArg (List.replicate 3) (Frame.sort_wire k h i)) (congrArg List.singleton (Frame.sort_wire k h i)))
    (congrArg (List.replicate 3) (Frame.sort_wire k h i)) (congrArg List.singleton (Frame.sort_wire k h i))

theorem rowBack_input (i : Frame.Resource k h) (b : Fin 3) :
    (rowBack (d := d) i).ports (.input ⟨b.val,by simp⟩) = .input ⟨(swap b).val,by simp⟩ := by
  rcases Frame.triple b with rfl | rfl | rfl <;> rfl

theorem rowBack_output (i : Frame.Resource k h) (b : Fin 1) :
    (rowBack (d := d) i).ports (.output b) = .output b := rfl

variable (H : Hypernet d [.term] (environmentInterface k h)) (R : ContractionTree .term n)

/-- Exchange only the two active payload slots; retain the full residual tree
and every original resource row slot. -/
def slot : (Frame.graph n k h d).Edge → (Frame.graph n k h d).Edge
  | .inl b => .inl (swap b)
  | .inr e => .inr e

theorem slot_slot (e : (Frame.graph n k h d).Edge) : slot (slot e) = e := by
  rcases e with b | e
  · exact congrArg Sum.inl (swap_swap b)
  · rfl

theorem slot_injective : Function.Injective (slot (d := d) (n := n) (k := k) (h := h)) := by
  intro a b eq
  have := congrArg slot eq
  simpa only [slot_slot] using this

noncomputable def component (e : (Frame.graph n k h d).Edge) :
    Occurrence (Frame.family H R true e) (Frame.family H R false (slot e)) := by
  cases d <;> rcases e with b | (j | i)
  all_goals first | exact Occurrence.ofIso (DeepIso.refl H) | exact Occurrence.ofIso (DeepIso.refl (R.atDepth _)) | exact rowBack i

noncomputable def each (e : (Frame.graph n k h d).Edge) :
    Occurrence (Frame.family H R true e)
      (CopyingInputPermutation.net (Frame.normal H R false) (exchangeInputs n)) :=
  ((component H R e).comp (Occurrence.expand _ (Frame.family H R false) (slot e))).comp
    (forward (Frame.normal H R false) (exchangeInputs n))

noncomputable def host : (Frame.graph n k h d).Vertex →
    (CopyingInputPermutation.net (Frame.normal H R false) (exchangeInputs n)).Vertex
  | .input i => .input i
  | .output i => .output i
  | .internal (.inl (b,i)) => .internal (.inl (.inl (swap b,i)))
  | .internal (.inr j) => .internal (.inl (.inr j))


theorem input (e : (Frame.graph n k h d).Edge) (i) :
    (each H R e).ports (.input i) = host H R ((Frame.graph n k h d).sourcePort e i) := by
  cases d <;> rcases e with b | (j | r)
  all_goals first
    | (change Fin 1 at i
       have zero : i=0 := Subsingleton.elim _ _
       subst i
       rcases Frame.triple b with rfl | rfl | rfl
       all_goals rfl)
    | (change Fin (List.replicate n Wire.term).length at i
       change (forward (Frame.normal H R false) (exchangeInputs n)).ports
         (Net.Expansion.insert (Frame.graph n k h _) (Frame.family H R false) (.inr (.inl j)) (.input i)) = _
       simp only [Net.Expansion.insert,Frame.graph,Net.relabel,Frame.net,Net.sourcePort,Frame.source,
         List.getElem_map,List.getElem_finRange]
       have bound : i.val < n := by simpa using i.isLt
       change Port.input ((exchangeInputs n).bijection.toFun ⟨i.val+2,by simp; omega⟩) =
         Port.input ⟨i.val+2,by simp; omega⟩
       apply congrArg Port.input
       simp [exchangeInputs,CopyingInputPermutation.swap,CopyingInputPermutation.exchange,Fin.ext_iff] <;> omega)
    | (change Fin 3 at i
       change (forward (Frame.normal H R false) (exchangeInputs n)).ports
         (Net.Expansion.insert (Frame.graph n k h _) (Frame.family H R false) (.inr (.inr r))
           ((rowBack r).ports (.input i))) = _
       rw [show (rowBack r).ports (.input i) = _ from rowBack_input r i]
       simp only [Net.Expansion.insert,Frame.graph,Net.relabel,Frame.net,Net.sourcePort,Frame.source,
         List.getElem_map,List.getElem_finRange]
       rfl)

theorem output (e : (Frame.graph n k h d).Edge) (i) :
    (each H R e).ports (.output i) = host H R ((Frame.graph n k h d).targetPort e i) := by
  cases d <;> rcases e with b | (j | r)
  all_goals first
    | (change Fin (environmentInterface k h).length at i
       change (forward (Frame.normal H R false) (exchangeInputs n)).ports
         (Net.Expansion.insert (Frame.graph n k h _) (Frame.family H R false) (.inl (swap b)) (.output i)) = _
       simp only [Net.Expansion.insert,Frame.graph,Net.relabel,Frame.net,Net.targetPort,Frame.target,
         List.getElem_map,List.getElem_finRange]
       rfl)
    | (change Fin 1 at i
       have zero : i=0 := Subsingleton.elim _ _
       subst i
       rfl)

theorem disjoint (e a : (Frame.graph n k h d).Edge) (different : e ≠ a) :
    ∀ b c, (each H R e).edges b ≠ (each H R a).edges c := by
  intro b c eq
  have eq : (slot e) = slot a := congrArg Sigma.fst eq
  exact different (slot_injective eq)

/-- Actual complete occurrence into the input-compensated opposite frame. -/
noncomputable def occurrence : Occurrence (Frame.normal H R true)
    (CopyingInputPermutation.net (Frame.normal H R false) (exchangeInputs n)) :=
  Occurrence.ExpansionJoin.occurrence _ _ (each H R) (host H R) (input H R) (output H R) (disjoint H R)


theorem cover (e : (CopyingInputPermutation.net (Frame.normal H R false) (exchangeInputs n)).Edge) :
    ∃ a, (occurrence H R).edges a = e := by
  cases d
  all_goals
    rcases e with ⟨e,a⟩
    rcases e with b | (j | i)
    · refine ⟨⟨.inl (swap b),a⟩,?_⟩
      change (⟨.inl (swap (swap b)),a⟩ : (Frame.normal H R false).Edge) = ⟨.inl b,a⟩
      exact congrArg (fun b : Fin 3 => (⟨.inl b,a⟩ : (Frame.normal H R false).Edge)) (swap_swap b)
    · exact ⟨⟨.inr (.inl j),a⟩,rfl⟩
    · exact ⟨⟨.inr (.inr i),a⟩,rfl⟩

/-- The fixed-boundary symmetry exchanges the first two identical payloads,
retains the entire remaining tree, and reverses the two resource-row inputs. -/
noncomputable def iso : DeepIso (Frame.normal H R true)
    (CopyingInputPermutation.net (Frame.normal H R false) (exchangeInputs n)) :=
  (occurrence H R).iso_of_edge_surjective (fun _ => rfl) (fun _ => rfl) (cover H R)

end Hypernets.Copying.CopyingDouble.Symmetry

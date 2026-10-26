import Hypernets.Copying.DepthLowering
import Hypernets.Copying.PaddingInteractions

/-! Truncation commutes with graph assembly, retaining all attachment coordinates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Lowering
open Graph

/-- Serial assembly and truncation have the same incidence. -/
noncomputable def serial_graph {d I J K} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) J K) :
    Net.Iso (graph (Serial.net G H)) (Serial.net (graph G) (graph H)) := by
  cases d <;> exact {
      vertices := {
        toFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        invFun := fun | .inl v => .inl v | .inr ⟨false,v⟩ => .inr ⟨false,v⟩ | .inr ⟨true,v⟩ => .inr ⟨true,v⟩
        left_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl
        right_inv := by rintro (v | ⟨a,v⟩); rfl; cases a <;> rfl }
      edges := {
        toFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        invFun := fun | ⟨false,f⟩ => ⟨false,f⟩ | ⟨true,f⟩ => ⟨true,f⟩
        left_inv := by rintro ⟨a,f⟩; cases a <;> rfl
        right_inv := by rintro ⟨a,f⟩; cases a <;> rfl }
      internal_label v := by rcases v with v | ⟨a,v⟩; rfl; cases a <;> rfl
      edge_label x := by rcases x with ⟨a,f⟩; cases a <;> rfl
      source x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.source f).map _).map _ = (G.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.source f).map _).map _ = (H.source f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
      target x := by
        rcases x with ⟨a,f⟩
        cases a
        · change ((G.target f).map _).map _ = (G.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
        · change ((H.target f).map _).map _ = (H.target f).map _
          simp only [List.map_map]
          apply List.map_congr_left
          intro v _
          cases v <;> simp [Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,Serial.pattern,List.getElem_map,Port.map]
    }

/-- A filled edge's interface is unchanged by truncation, with explicit equality casts. -/
def expandFilling {d I O} (C : Hypernet (d+1) I O)
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) (e : C.Edge) :=
  (graph (F e)).reboundary (label_input d (C.edgeLabel e)).symm
    (label_output d (C.edgeLabel e)).symm

/-- The input and output casts do not move the attachment in the truncated host. -/
theorem expand_insert {d I O} (C : Hypernet (d+1) I O)
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) (e : C.Edge) (v : (F e).Vertex) :
    Net.Expansion.insert (graph C) (expandFilling C F) e
      (Port.cast (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm v) =
    Net.Expansion.insert C F e v := by
  cases v <;> simp [expandFilling,Net.Expansion.insert,Net.Expansion.host,Net.sourcePort,Net.targetPort,
    graph,Net.relabel,Port.cast]

/-- Simultaneous assembly commutes with truncation on the actual finite carriers. -/
noncomputable def expand_graph {d I O} (C : Hypernet (d+1) I O)
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) :
    Net.Iso (graph (C.expand F)) ((graph C).expand (expandFilling C F)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := rfl
  source e := by
    simp only [graph,Net.relabel,Net.expand,Net.Expansion.source,expandFilling,Net.reboundary,
      Bijection.refl,Port.map_id_fun,List.map_map]
    apply List.map_congr_left
    intro v _
    exact (expand_insert C F e.1 v).symm
  target e := by
    simp only [graph,Net.relabel,Net.expand,Net.Expansion.target,expandFilling,Net.reboundary,
      Bijection.refl,Port.map_id_fun,List.map_map]
    apply List.map_congr_left
    intro v _
    exact (expand_insert C F e.1 v).symm

/-- The same attachment equation for a single selected slot. -/
theorem plug_insert {d I O} (C : Hypernet (d+1) I O) (e : C.Edge)
    (G : Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) (v : G.Vertex) :
    Net.Replacement.insert (graph C) e
      ((graph G).reboundary (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm)
      (Port.cast (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm v) =
    Net.Replacement.insert C e G v := by
  cases v <;> simp [Net.Replacement.insert,Net.Replacement.host,Net.sourcePort,Net.targetPort,
    graph,Net.relabel,Port.cast]
/-- Single-slot assembly commutes with truncation without a cast on the original filler. -/
noncomputable def plug_graph {d I O} (C : Hypernet (d+1) I O) (e : C.Edge)
    (G : Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) :
    Net.Iso (graph (C.plug e G)) ((graph C).plug e
      ((graph G).reboundary (label_input d (C.edgeLabel e)).symm (label_output d (C.edgeLabel e)).symm)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := by cases e <;> rfl
  source x := by
    cases x with
    | inl x => simp [graph,Net.relabel,Bijection.refl,Net.Replacement.source,Net.Replacement.host]
    | inr x =>
      simp only [graph,Net.relabel,Net.plug,Net.Replacement.source,Net.reboundary,
        Bijection.refl,Port.map_id_fun,List.map_map]
      apply List.map_congr_left
      intro v _
      exact (plug_insert C e G v).symm
  target x := by
    cases x with
    | inl x => simp [graph,Net.relabel,Bijection.refl,Net.Replacement.target,Net.Replacement.host]
    | inr x =>
      simp only [graph,Net.relabel,Net.plug,Net.Replacement.target,Net.reboundary,
        Bijection.refl,Port.map_id_fun,List.map_map]
      apply List.map_congr_left
      intro v _
      exact (plug_insert C e G v).symm


/-- Truncation changes neither a primitive nor its corolla incidence. -/
theorem primitive (d : Nat) (p : Primitive) :
    graph (primitiveNet (d+1) p) = primitiveNet d p := by cases d <;> rfl

/-- Equality casts of the ordered interface commute with truncation. -/
theorem castInterfaces {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet (d+1) I O) :
    graph (Translation.castInterfaces hi ho G) = Translation.castInterfaces hi ho (graph G) := by
  cases hi; cases ho; rfl

/-- A representability certificate is insensitive to interface equality casts. -/
theorem fits_castInterfaces {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet (d+1) I O) :
    Fits (Translation.castInterfaces hi ho G) ↔ Fits G := by cases hi; cases ho; rfl

theorem fits_reboundary {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet (d+1) I O) :
    Fits (G.reboundary hi ho) ↔ Fits G := Iff.rfl

/-- Serial expansion retains exactly the two components' depth obligations. -/
theorem fits_serial {d I J O} (G : Hypernet (d+1) I J) (H : Hypernet (d+1) J O) :
    Fits (Serial.net G H) ↔ Fits G ∧ Fits H := by
  constructor
  · intro fit; exact ⟨fun e => fit ⟨false,e⟩,fun e => fit ⟨true,e⟩⟩
  · rintro ⟨g,h⟩ ⟨b,e⟩; cases b
    · exact g e
    · exact h e

/-- Parallel juxtaposition retains exactly its components' depth obligations. -/
theorem fits_tensor {d I O J K} (G : Hypernet (d+1) I O) (H : Hypernet (d+1) J K) :
    Fits (Net.Tensor.net G H) ↔ Fits G ∧ Fits H :=
  Net.Tensor.labels_iff G H (FitsLabel d)

/-- The erased host slot needs no depth certificate; every surviving label does. -/
theorem fits_plug {d I O} (C : Hypernet (d+1) I O) (e : C.Edge)
    (G : Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) :
    Fits (C.plug e G) ↔ (∀ b, b ≠ e → FitsLabel d (C.edgeLabel b)) ∧ Fits G := by
  constructor
  · intro fit; exact ⟨fun b ne => fit (.inl ⟨b,ne⟩),fun b => fit (.inr b)⟩
  · rintro ⟨c,g⟩ (b | b)
    · exact c b.val b.property
    · exact g b

/-- Simultaneous expansion erases all skeleton labels. -/
theorem fits_expand {d I O} (C : Hypernet (d+1) I O)
    (F : (e : C.Edge) → Hypernet (d+1) ((alphabet (d+1)).signature.input (C.edgeLabel e))
      ((alphabet (d+1)).signature.output (C.edgeLabel e))) :
    Fits (C.expand F) ↔ ∀ e, Fits (F e) := by
  constructor
  · intro fit e b; exact fit ⟨e,b⟩
  · intro fit e; exact fit e.1 e.2

/-- A box at the very first layer cannot lose an allowance. -/
theorem box_not_fits {bound k h} (G : Hypernet 0 [.term] (environmentInterface (bound+k) h)) :
    ¬ Fits (Copying.box G) := fun fit => fit (0 : Fin 1)

/-- Higher boxes fit exactly when their bodies fit. -/
theorem fits_box {d bound k h} (G : Hypernet (d+1) [.term] (environmentInterface (bound+k) h)) :
    Fits (Copying.box G) ↔ Fits G := by
  constructor
  · intro fit; exact fit (0 : Fin 1)
  · intro fit e; exact fit

/-- Truncation acts recursively on box bodies and preserves all binder metadata. -/
theorem box {d bound k h} (G : Hypernet (d+1) [.term] (environmentInterface (bound+k) h)) :
    graph (Copying.box G) = Copying.box (lower d G) := rfl

/-- The original bound-variable ordering is retained. -/
theorem lambdaBox {d k h} (G : Hypernet (d+1) [.term] (environmentInterface (k+1) h)) :
    graph (Translation.lambdaBox G) = Translation.lambdaBox (graph G) := by
  unfold Translation.lambdaBox
  rw [box, ← graph_eq_lower, castInterfaces]

/-- Lambda payload assembly commutes with truncation. -/
noncomputable def lambdaPayload {d k h}
    (G : Hypernet (d+1) [.term] (environmentInterface (k+1) h)) :
    DeepIso (graph (Copying.lambdaPayload G)) (Copying.lambdaPayload (graph G)) := by
  simpa only [Copying.lambdaPayload,primitive,lambdaBox] using
    DeepIso.ofIso (serial_graph (primitiveNet (d+2) (.operation .lam)) (Translation.lambdaBox G))

/-- Every non-excessive primitive remains exactly the same primitive. -/
theorem primitive_iff (d : Nat) (a : (alphabet (d+1)).Symbol) (fit : FitsLabel d a) (p : Primitive) :
    a = primitiveLabel (d+1) p ↔ label d a = primitiveLabel d p := by
  cases d with
  | zero => cases a with
    | inl a =>
      constructor <;> intro eq <;> cases eq <;> rfl
    | inr b => exact False.elim fit
  | succ d => cases a with
    | inl a => constructor <;> intro eq <;> cases eq <;> rfl
    | inr b => simp [label, primitiveLabel]

/-- All primitive restrictions survive truncation on its representable domain. -/
theorem labelAll_iff (P : Primitive → Prop) (d : Nat) (a : (alphabet (d+1)).Symbol)
    (fit : FitsLabel d a) : LabelAll P d (label d a) ↔ LabelAll P (d+1) a := by
  induction d with
  | zero => cases a with
    | inl p => rfl
    | inr b => exact False.elim fit
  | succ d ih => cases a with
    | inl p => rfl
    | inr b =>
      change AllLabels P (lower d b.body) ↔ AllLabels P b.body
      rw [← graph_eq_lower]
      constructor <;> intro h e
      · exact (ih _ (fit e)).mp (h e)
      · exact (ih _ (fit e)).mpr (h e)

theorem allLabels_iff (P : Primitive → Prop) {d I O} (G : Hypernet (d+1) I O) (fit : Fits G) :
    AllLabels P (graph G) ↔ AllLabels P G := by
  constructor <;> intro h e
  · exact (labelAll_iff P d _ (fit e)).mp (h e)
  · exact (labelAll_iff P d _ (fit e)).mpr (h e)

/-- Exact intrinsic-search transport, valid for every representable graph. -/
def search {d I O} (G : Hypernet (d+1) I O) (fit : Fits G) : Search.Transport G (graph G) where
  ports := Bijection.refl _
  edges := Bijection.refl _
  primitive e p := primitive_iff d (G.edgeLabel e) (fit e) p
  source e := by simp [graph,Net.relabel,Bijection.refl]
  target e := by simp [graph,Net.relabel,Bijection.refl]
  input_iff v := Iff.rfl

end Hypernets.Copying.Lowering

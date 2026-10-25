import Hypernets.Copying.BinaryContextPlug

/-! Padding is a representation change, and commutes with actual replacement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

/-- Reindex a local hole interface before filling it. -/
theorem plugAt_castInterfaces {d I O} {G : Hypernet d I O} {r J K J' K'}
    (hi : J = J') (ho : K = K') (s : Site G r J K) (A : Hypernet r J' K') :
    plugAt (s.castInterfaces hi ho) A = plugAt s (A.reboundary hi.symm ho.symm) := by
  cases hi; cases ho
  simp only [Site.castInterfaces,Net.reboundary_refl]

/-- Transport an address along equality of its host graph. -/
def Site.castGraph {d I O} {G H : Hypernet d I O} (eq : G = H)
    {r U V} (s : Site G r U V) : Site H r U V := eq ▸ s

theorem plugAt_castGraph {d I O} {G H : Hypernet d I O} (eq : G = H)
    {r U V} (s : Site G r U V) (A : Hypernet r U V) :
    plugAt (s.castGraph eq) A = plugAt s A := by cases eq; rfl

namespace Padding
/-- The label map of the existing recursive increase of allowance. -/
def label : (d : Nat) → (alphabet d).Symbol → (alphabet (d+1)).Symbol
  | 0, p => .inl p.down
  | _+1, .inl p => .inl p
  | d+1, .inr b => .inr ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩

theorem label_input (d : Nat) (p : (alphabet d).Symbol) :
    (alphabet (d+1)).signature.input (label d p) = (alphabet d).signature.input p := by
  cases d with
  | zero => rfl
  | succ d => cases p <;> rfl

theorem label_output (d : Nat) (p : (alphabet d).Symbol) :
    (alphabet (d+1)).signature.output (label d p) = (alphabet d).signature.output p := by
  cases d with
  | zero => rfl
  | succ d => cases p <;> rfl

/-- A uniform relabelling presentation with definitionally unchanged outer carriers. -/
def graph {d I O} (G : Hypernet d I O) : Hypernet (d+1) I O :=
  G.relabel _ (label d) (label_input d) (label_output d)

theorem graph_eq_raise {d I O} (G : Hypernet d I O) : graph G = raise d G := by
  cases d with
  | zero => rfl
  | succ d =>
    unfold graph raise
    congr 1
    funext p
    cases p <;> rfl

/-- Shallow replacement and one-step padding have identical ordered incidence. -/
noncomputable def plug {d I O J K} (C : Hypernet d I O) (e : C.Edge)
    (G : Hypernet d J K)
    (hi : J = (alphabet d).signature.input (C.edgeLabel e))
    (ho : K = (alphabet d).signature.output (C.edgeLabel e)) :
    Net.Iso (graph (C.plug e (G.reboundary hi ho)))
      ((graph C).plug e ((graph G).reboundary
        (hi.trans (label_input d _).symm) (ho.trans (label_output d _).symm))) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := by cases v <;> rfl
  edge_label e := by cases e <;> rfl
  source x := by
    cases x with
    | inl x =>
      change ((C.source x.val).map _).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    | inr x =>
      change (((G.source x).map (Port.cast hi ho)).map _).map (Port.map id) = _
      simp only [Bijection.refl,Net.Replacement.source,Net.reboundary,graph,Net.relabel,List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Function.comp_apply,Port.cast,Net.Replacement.insert,
        Net.Replacement.host,Port.map_id_fun,Net.sourcePort,Net.targetPort]
  target x := by
    cases x with
    | inl x =>
      change ((C.target x.val).map _).map (Port.map id) = _
      rw [List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> rfl
    | inr x =>
      change (((G.target x).map (Port.cast hi ho)).map _).map (Port.map id) = _
      simp only [Bijection.refl,Net.Replacement.target,Net.reboundary,graph,Net.relabel,List.map_map]
      apply List.map_congr_left
      intro v _
      cases v <;> simp [Function.comp_apply,Port.cast,Net.Replacement.insert,
        Net.Replacement.host,Port.map_id_fun,Net.sourcePort,Net.targetPort]

/-- Padding a modified box is the same outer relabelling as modifying its padded box. -/
noncomputable def replaceBox_iso {d I O} (C : Hypernet (d+1) I O) (e : C.Edge)
    (b : Box (alphabet d)) (eq : C.edgeLabel e = .inr b)
    (A : Hypernet d [.term] (environmentInterface (b.bound+b.freeVariables) b.freeAtoms)) :
    Net.Iso (raise (d+1) (replaceBox C e b eq A))
      (replaceBox (raise (d+1) C) e
        ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩
        (by simp only [raise,Net.relabel,eq]) (raise d A)) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label v := rfl
  edge_label x := by
    classical
    by_cases he : x = e
    · subst x; simp [raise,replaceBox,Net.relabel,Net.relabelEdges,Bijection.refl]
    · simp [raise,replaceBox,Net.relabel,Net.relabelEdges,Bijection.refl,he]
  source x := by change (C.source x).map (Port.map id) = C.source x; simp
  target x := by change (C.target x).map (Port.map id) = C.target x; simp

/-- Increase both the host allowance and the local hole allowance by one. -/
noncomputable def site {d I O} {G : Hypernet d I O} {r U V} (s : Site G r U V) :
    Site (raise d G) (r+1) U V := by
  induction s with
  | @shallow d I O C e =>
    have s' := (Site.shallow (graph C) e).castInterfaces (label_input d _) (label_output d _)
    exact s'.castGraph (graph_eq_raise C)
  | @inside d I O C e b eq r U V inner ih =>
    exact @Site.inside (d+1) I O (raise (d+1) C) e ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩
      (by simp only [raise,Net.relabel,eq]) (r+1) U V ih

/-- One-step padding commutes with arbitrary-depth addressed filling. -/
noncomputable def filling {d I O} {G : Hypernet d I O} {r U V}
    (s : Site G r U V) (A : Hypernet r U V) :
    DeepIso (raise d (plugAt s A)) (plugAt (site s) (raise r A)) := by
  induction s with
  | @shallow d I O C e =>
    have f := DeepIso.ofIso (plug C e A rfl rfl)
    simp only [Net.reboundary_refl] at f
    unfold site
    rw [plugAt_castGraph, plugAt_castInterfaces]
    simpa only [graph_eq_raise,plugAt] using f
  | @inside d I O C e b eq r U V inner ih =>
    exact (DeepIso.ofIso (replaceBox_iso C e b eq (plugAt inner A))).trans
      (replaceBox_deepIso (raise (d+1) C) e
        ⟨b.bound,b.freeVariables,b.freeAtoms,raise d b.body⟩
        (by simp only [raise,Net.relabel,eq]) (ih A))
/-- Equality transport preserves the certificate on the very same occurrence. -/
theorem site_castGraph_sole {d I O} {G H : Hypernet d I O} (eq : G = H)
    {r U V} (s : Site G r U V) (sole : SoleHole s) : SoleHole (s.castGraph eq) := by
  cases eq; exact sole

/-- Padding keeps every other outer edge hole-free. -/
theorem graph_other_free {d I O} (G : Hypernet d I O) (e : G.Edge)
    (free : ∀ f, f ≠ e → LabelAll (fun p => ∀ h, p ≠ .hole h) d (G.edgeLabel f)) :
    ∀ f, f ≠ e → LabelAll (fun p => ∀ h, p ≠ .hole h) (d+1) ((graph G).edgeLabel f) := by
  intro f ne
  have h := (SingleHole.freeLabel_raise d G f).mpr (free f ne)
  cases d with
  | zero => exact h
  | succ d =>
    cases eq : G.edgeLabel f <;>
      simpa only [raise,graph,Net.relabel,StoreTrace.paddingEdges,Bijection.refl,id_eq,eq,label] using h

/-- The lifted address remains the sole occurrence, including below padded boxes. -/
theorem site_sole {d I O} {G : Hypernet d I O} {r U V}
    (s : Site G r U V) (sole : SoleHole s) : SoleHole (site s) := by
  induction s with
  | @shallow d I O C e =>
    apply site_castGraph_sole
    apply SoleHole.castInterfaces
    refine ⟨?_,graph_other_free C e sole.2⟩
    obtain ⟨h,eq⟩ := sole.1
    refine ⟨h,?_⟩
    change label d (C.edgeLabel e) = primitiveLabel (d+1) (.hole h)
    rw [eq]
    cases d <;> rfl
  | @inside d I O C e b eq r U V inner ih =>
    refine ⟨ih sole.1,?_⟩
    intro f ne
    have h := graph_other_free C e sole.2 f ne
    cases eq : C.edgeLabel f <;>
      simpa only [raise,graph,Net.relabel,eq,label] using h

/-- Recursive isomorphism is preserved by the original one-step padding. -/
noncomputable def congr {d I O} {G H : Hypernet d I O} (f : DeepIso G H) :
    DeepIso (raise d G) (raise d H) := by
  induction d generalizing I O with
  | zero =>
    exact {
      vertices := f.vertices
      edges := f.edges
      internal_label := f.internal_label
      source := f.source
      target := f.target
      edge_label := fun e => congrArg ULift.down (f.edge_label e) }
  | succ d ih =>
    refine {
      vertices := f.vertices
      edges := f.edges
      internal_label := f.internal_label
      source := f.source
      target := f.target
      edge_label := ?_ }
    intro e
    have h := f.edge_label e
    simp only [raise, Net.relabel]
    generalize G.edgeLabel e = a at *
    generalize H.edgeLabel (f.edges.toFun e) = b at *
    cases a with
    | inl a => cases b with
      | inl b => exact h
      | inr b => exact False.elim h
    | inr a => cases b with
      | inl b => exact False.elim h
      | inr b =>
        cases h with
        | bodies related =>
          obtain ⟨g⟩ := related
          exact BoxRelated.bodies ⟨ih g⟩

/-- Carry an address through any finite amount of the existing padding. -/
noncomputable def padSite {d I O} {G : Hypernet d I O} {r U V}
    (s : Site G r U V) : (n : Nat) → Site (Translation.pad d n G) (r+n) U V
  | 0 => s
  | n+1 => site (padSite s n)

/-- Recursive isomorphisms commute with iterated padding. -/
noncomputable def pad_congr {d I O} {G H : Hypernet d I O}
    (f : DeepIso G H) : (n : Nat) →
      DeepIso (Translation.pad d n G) (Translation.pad d n H)
  | 0 => f
  | n+1 => congr (pad_congr f n)

/-- Iterated padding commutes with actual deep filling, raising the local
allowance by exactly the same amount as the host allowance. -/
noncomputable def pad_filling {d I O} {G : Hypernet d I O} {r U V}
    (s : Site G r U V) (A : Hypernet r U V) (n : Nat) :
    DeepIso (Translation.pad d n (plugAt s A))
      (plugAt (padSite s n) (Translation.pad r n A)) := by
  induction n with
  | zero => exact DeepIso.refl _
  | succ n ih => exact (congr ih).trans (filling (padSite s n) (Translation.pad r n A))

/-- Any finite padding retains the sole-hole certificate on the lifted address. -/
theorem padSite_sole {d I O} {G : Hypernet d I O} {r U V}
    (s : Site G r U V) (sole : SoleHole s) (n : Nat) : SoleHole (padSite s n) := by
  induction n with
  | zero => exact sole
  | succ n ih => exact site_sole _ ih

end Padding
end Hypernets.Copying

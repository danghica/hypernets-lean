import Hypernets.Copying.OperationalInputSafety

/-! Padding and flat-stability laws for the unchanged operational templates. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates
open Graph

/-- Both original operational graph pairs survive allowance padding, with
the body, stable argument and interfaces retained. -/
theorem Pair.raise {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    Pair kind (Copying.raise d G) (Copying.raise d H) := by
  cases pair with
  | witness f pair g =>
    cases pair with
    | beta B A free stable =>
      exact .witness ((Padding.congr f).trans (Application.before_raise B A))
        (.beta _ _ ((allLabels_raise_iff _ _ _).mpr free) ((Stable.raise_iff _).mpr stable))
        ((Application.after_raise B A).symm.trans (Padding.congr g))
    | reference A stable =>
      exact .witness ((Padding.congr f).trans (Allocation.before_raise A))
        (.reference _ ((Stable.raise_iff _).mpr stable))
        ((Allocation.after_raise A).symm.trans (Padding.congr g))

theorem template_paddingClosed (kind : Kind) : (template kind).PaddingClosed := @Pair.raise kind

/-- A beta reduct still contains the original body with its bound term output.
Flat stable labels cannot produce that output. -/
theorem beta_after_not_stable_labels {d k h O}
    (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) :
    ¬ ∀ e, StableLabel (d+1) ((Application.after B G).edgeLabel e) := by
  intro labels
  have body : Stable (Application.openBody B) := Stable.of_labels (fun e => labels ⟨false,e⟩)
  exact body.outputs (0 : Fin (_+1))

/-- Neither side is a flat stable fragment: the left retains its active head,
and the right retains either the opened bound output or the newly created store. -/
theorem Literal.not_stable_labels {kind d I O} {G H : Hypernet d I O}
    (pair : Literal kind G H) :
    (¬ ∀ e, StableLabel d (G.edgeLabel e)) ∧ (¬ ∀ e, StableLabel d (H.edgeLabel e)) := by
  cases pair with
  | beta B G free stable =>
    refine ⟨?_,beta_after_not_stable_labels B G⟩
    intro labels
    obtain ⟨p,label,passive⟩ := labels (Application.head B G)
    have eq := primitiveLabel_injective _ ((Application.localMatch B G).head_at.1.symm.trans label)
    subst p
    cases passive
  | reference G stable =>
    refine ⟨?_,fun labels => Allocation.after_not_stable G (Stable.of_labels labels)⟩
    intro labels
    obtain ⟨p,label,passive⟩ := labels (Allocation.head G)
    have eq := primitiveLabel_injective _ ((Allocation.head_at G).1.symm.trans label)
    subst p
    cases passive

theorem Pair.not_stable_labels {kind d I O} {G H : Hypernet d I O} (pair : Pair kind G H) :
    (¬ ∀ e, StableLabel d (G.edgeLabel e)) ∧ (¬ ∀ e, StableLabel d (H.edgeLabel e)) := by
  cases pair with
  | witness f pair g =>
    exact ⟨fun labels => pair.not_stable_labels.1 ((stableLabels_iso f).mp labels),
      fun labels => pair.not_stable_labels.2 ((stableLabels_iso g).mpr labels)⟩

theorem template_preservesStableLabels (kind : Kind) : (template kind).PreservesStableLabels := by
  intro d I O G H pair
  exact ⟨fun labels => False.elim (pair.not_stable_labels.1 labels),
    fun labels => False.elim (pair.not_stable_labels.2 labels)⟩

/-- A flat stable argument has no operational occurrence, shallow or deep;
its recursive certificate contains only retained edge corollas. -/
theorem stable_edge_retained {kind d I O} {C : Hypernet d I O} {L R e}
    (edge : DeepFillingEdge (template kind) C L R e)
    (labels : ∀ x, StableLabel d ((L e).edgeLabel x)) :
    Nonempty (LabelCopy (L e) (C.edgeLabel e) × LabelCopy (R e) (C.edgeLabel e)) := by
  cases edge with
  | retained l r => exact ⟨l,r⟩
  | filled h label rel => exact False.elim (rel.not_stable_labels.1 labels)
  | boxed b label inner l r =>
    have impossible := labels l.edge
    rw [l.edge_label] at impossible
    obtain ⟨p,eq,_⟩ := impossible
    cases eq

noncomputable def stable_expansion_iso {kind d I O} {C : Hypernet d I O} {L R}
    (edges : ∀ e, DeepFillingEdge (template kind) C L R e)
    (labels : ∀ x, StableLabel d ((C.expand L).edgeLabel x)) :
    DeepIso (C.expand L) (C.expand R) := by
  let copies e := Classical.choice (stable_edge_retained (edges e) (fun x => labels ⟨e,x⟩))
  exact (DeepIso.ofIso (FillingCollapse.identity C L (fun e => (copies e).1))).trans
    (DeepIso.ofIso (FillingCollapse.identity C R (fun e => (copies e).2))).symm

/-- Stable payloads agree up to ordered graph representation, not merely a
conditional observational relation. -/
noncomputable def stable_witness_iso {kind d O} {G H : Hypernet d [.term] O}
    (w : FillingWitness (template kind) G H) (stable : Stable G) : DeepIso G H :=
  w.leftIso.symm.trans ((stable_expansion_iso w.edges
    ((stableLabels_iso w.leftIso).mpr stable.labels)).trans w.rightIso)

end Hypernets.Copying.OperationalTemplates

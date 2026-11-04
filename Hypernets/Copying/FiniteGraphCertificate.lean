import Hypernets.Copying.ClosedTranslationUnits
import Hypernets.Graph.PathRank

/-! Kernel-checked finite tables for concrete ordered graph isomorphisms.
Tables are only candidate maps: both inverse laws, all labels and every
ordered incidence are proof obligations. No graph equality is postulated. -/
syntax "graph_decide_eq" : tactic
macro_rules
  | `(tactic| graph_decide_eq) => `(tactic|
    first
    | exact inferInstance
    | exact (inferInstance : DecidableEq Empty)
    | exact (inferInstance : DecidableEq (Fin _))
    | exact (inferInstance : DecidableEq Bool)
    | (refine @instDecidableEqSum _ _ ?_ ?_ <;> graph_decide_eq)
    | (refine @instDecidableEqSigma _ _ ?_ ?_
       · graph_decide_eq
       · intro b; cases b <;> graph_decide_eq))

namespace Hypernets.Copying.FiniteGraphCertificate
open Graph

def table {α β : Type} [BEq α] (domain : List α) (values : List β) (fallback : β) (a : α) : β :=
  (values[domain.idxOf a]?).getD fallback

theorem all {α : Type} (E : Enumeration α) (P : α → Prop)
    (checked : ∀ a ∈ E.elements, P a) : ∀ a, P a := fun a => checked a (E.complete a)

def emptyBijection {α β : Type} (A : Enumeration α) (B : Enumeration β)
    (ha : A.elements = []) (hb : B.elements = []) : Bijection α β := by
  have a (x : α) : False := by have h := A.complete x; rw [ha] at h; exact List.not_mem_nil h
  have b (x : β) : False := by have h := B.complete x; rw [hb] at h; exact List.not_mem_nil h
  exact ⟨fun x => False.elim (a x),fun x => False.elim (b x),
    fun x => False.elim (a x),fun x => False.elim (b x)⟩

/-- A supplied finite table is accepted only after its two inverse equations. -/
def bijection {α β : Type} (A : Enumeration α) (B : Enumeration β)
    (f : α → β) (g : β → α)
    (left : ∀ a ∈ A.elements, g (f a) = a)
    (right : ∀ b ∈ B.elements, f (g b) = b) : Bijection α β :=
  ⟨f,g,all A _ left,all B _ right⟩

/-- All edges and internal vertices are checked against their original finite
inventories. External ports are fixed, and source/target lists stay ordered. -/
def iso {d I O} (G H : Hypernet d I O)
    (v : Bijection G.Internal H.Internal) (e : Bijection G.Edge H.Edge)
    (labels : ∀ x ∈ G.finiteEdge.elements, LabelEquiv d (G.edgeLabel x) (H.edgeLabel (e.toFun x)))
    (types : ∀ x ∈ G.finiteInternal.elements, H.internalLabel (v.toFun x) = G.internalLabel x)
    (sources : ∀ x ∈ G.finiteEdge.elements,
      (G.source x).map (Port.map v.toFun) = H.source (e.toFun x))
    (targets : ∀ x ∈ G.finiteEdge.elements,
      (G.target x).map (Port.map v.toFun) = H.target (e.toFun x)) : DeepIso G H where
  vertices := v
  edges := e
  internal_label := all G.finiteInternal _ types
  edge_label := all G.finiteEdge _ labels
  source := all G.finiteEdge _ sources
  target := all G.finiteEdge _ targets
/-- Finite incidence checks certify a strictly increasing edge rank. -/
theorem path_nodup {d I O} (G : Hypernet d I O) (rank : G.Edge → Nat)
    (checked : ∀ e ∈ G.finiteEdge.elements, ∀ f ∈ G.finiteEdge.elements,
      ∀ v ∈ G.target e, v ∈ G.source f → rank e < rank f)
    {es} (path : G.Path es) : es.Nodup :=
  G.path_nodup_of_rank rank (fun {e f} ⟨v,hv,hf⟩ =>
    checked e (G.finiteEdge.complete e) f (G.finiteEdge.complete f) v hv hf) path
end Hypernets.Copying.FiniteGraphCertificate

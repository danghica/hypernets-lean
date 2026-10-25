import Hypernets.Copying.BoundaryParallel

/-! Boundary renaming through the literal instance-edge prefix of atom translation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.InstancePrefix
open Graph

def graph {d O} (H : Hypernet d [.atom] O) := Serial.net (primitiveNet d .instanceEdge) H

def ports {d O} (H : Hypernet d [.atom] O) : Bijection (graph H).Vertex (Unit ⊕ H.Vertex) := by
  cases d
  all_goals
    exact {
      toFun
        | .input _ => .inl ()
        | .output j => .inr (.output j)
        | .internal (.inl j) => .inr (.input j)
        | .internal (.inr ⟨false,v⟩) => nomatch v
        | .internal (.inr ⟨true,v⟩) => .inr (.internal v)
      invFun
        | .inl _ => .input ⟨0,by change 0 < 1; decide⟩
        | .inr (.input j) => .internal (.inl j)
        | .inr (.output j) => .output j
        | .inr (.internal v) => .internal (.inr ⟨true,v⟩)
      left_inv v := by
        cases v with
        | input j => apply congrArg Port.input; apply Fin.ext; have := j.isLt; change j.val < 1 at this; change 0 = j.val; omega
        | output j => rfl
        | internal v => cases v with
          | inl j => rfl
          | inr v => rcases v with ⟨b,v⟩; cases b; exact nomatch v; rfl
      right_inv v := by cases v with
        | inl u => cases u; rfl
        | inr v => cases v <;> rfl
    }

def liftPorts {d O K} {H : Hypernet d [.atom] O} {H' : Hypernet d [.atom] K}
    (f : BoundaryIso H H') : Bijection (graph H).Vertex (graph H').Vertex :=
  (ports H).trans (((Bijection.refl Unit).sum f.ports).trans (ports H').symm)

theorem input_fixed {d O K} {H : Hypernet d [.atom] O} {H' : Hypernet d [.atom] K}
    (f : BoundaryIso H H') : f.ports.toFun (.input 0) = .input 0 := by
  have h := (f.input_iff (.input 0)).mpr trivial
  cases eq : f.ports.toFun (.input 0) with
  | internal v => simp [eq,Port.IsInput] at h
  | output j => simp [eq,Port.IsInput] at h
  | input j => congr 1; apply Fin.ext; have := j.isLt; change j.val < 1 at this; change j.val = 0; omega

/-- Every old port is embedded unchanged except that the old input becomes internal. -/
def embed {d O} (H : Hypernet d [.atom] O) (v : H.Vertex) : (graph H).Vertex :=
  (ports H).invFun (.inr v)

theorem lift_embed {d O K} {H : Hypernet d [.atom] O} {H' : Hypernet d [.atom] K}
    (f : BoundaryIso H H') (v : H.Vertex) :
    (liftPorts f).toFun (embed H v) = embed H' (f.ports.toFun v) := by
  simp [liftPorts,embed,Bijection.trans,Bijection.symm,(ports H).right_inv,Bijection.sum]



theorem vertex_embed {d O} (H : Hypernet d [.atom] O) (v : H.Vertex) :
    (graph H).vertexLabel (embed H v) = H.vertexLabel v := by
  cases d <;> cases v <;> rfl

theorem input_embed {d O} (H : Hypernet d [.atom] O) (v : H.Vertex) :
    ¬ (embed H v).IsInput := by cases d <;> cases v <;> simp [embed,ports,Port.IsInput]

theorem output_embed {d O} (H : Hypernet d [.atom] O) (v : H.Vertex) :
    (embed H v).IsOutput ↔ v.IsOutput := by cases d <;> cases v <;> rfl

def insert {d O} (H : Hypernet d [.atom] O) : H.Vertex → (graph H).Vertex := by
  cases d with
  | zero => exact Net.Expansion.insert (Serial.pattern 0 [.term] [.atom] O) (Serial.filling (primitiveNet 0 .instanceEdge) H) true
  | succ d => exact Net.Expansion.insert (Serial.pattern (d+1) [.term] [.atom] O) (Serial.filling (primitiveNet (d+1) .instanceEdge) H) true

theorem insert_eq_embed {d O} (H : Hypernet d [.atom] O) (v : H.Vertex) : insert H v = embed H v := by
  cases d
  all_goals
    cases v with
    | internal v => rfl
    | input j =>
      have hj : j = 0 := Fin.ext (by have := j.isLt; change j.val < 1 at this; change j.val = 0; omega)
      subst j
      rfl
    | output j =>
      change Port.map Sum.inl ((Serial.pattern 0 [.term] [.atom] O).targetPort true j) = Port.output j
      simp [Net.targetPort,Serial.pattern,List.getElem_map,Port.map]

def edges {d O K} {H : Hypernet d [.atom] O} {H' : Hypernet d [.atom] K}
    (f : BoundaryIso H H') : Bijection (graph H).Edge (graph H').Edge := by
  cases d
  all_goals exact {
    toFun := fun | ⟨false,e⟩ => ⟨false,e⟩ | ⟨true,e⟩ => ⟨true,f.edges.toFun e⟩
    invFun := fun | ⟨false,e⟩ => ⟨false,e⟩ | ⟨true,e⟩ => ⟨true,f.edges.invFun e⟩
    left_inv := by rintro ⟨b,e⟩; cases b; rfl; simp [f.edges.left_inv]
    right_inv := by rintro ⟨b,e⟩; cases b; rfl; simp [f.edges.right_inv] }

def iso {d O K} {H : Hypernet d [.atom] O} {H' : Hypernet d [.atom] K}
    (f : BoundaryIso H H') : BoundaryIso (graph H) (graph H') where
  ports := liftPorts f
  edges := edges f
  vertex_label v := by
    have hv := (ports H).left_inv v
    generalize hx : (ports H).toFun v = x at hv
    cases x with
    | inl x => cases x; subst v; cases d <;> rfl
    | inr w =>
      change embed H w = v at hv
      subst v
      rw [lift_embed,vertex_embed,vertex_embed]
      exact f.vertex_label w
  input_iff v := by
    have hv := (ports H).left_inv v
    generalize hx : (ports H).toFun v = x at hv
    cases x with
    | inl x => cases x; subst v; cases d <;> rfl
    | inr w =>
      change embed H w = v at hv
      subst v
      rw [lift_embed]
      exact iff_of_false (input_embed H' _) (input_embed H _)
  output_iff v := by
    have hv := (ports H).left_inv v
    generalize hx : (ports H).toFun v = x at hv
    cases x with
    | inl x => cases x; subst v; cases d <;> rfl
    | inr w =>
      change embed H w = v at hv
      subst v
      rw [lift_embed,output_embed,output_embed]
      exact f.output_iff w
  edge_label e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals first | exact labelEquiv_refl _ _ | exact f.edge_label e
  source e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals try rfl
    all_goals
      change ((H.source e).map _).map _ = (H'.source (f.edges.toFun e)).map _
      rw [← f.source e]
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      have law := lift_embed f v
      change (liftPorts f).toFun (insert H v) = insert H' (f.ports.toFun v)
      simpa only [insert_eq_embed] using law
  target e := by
    cases d <;> rcases e with ⟨b,e⟩ <;> cases b
    all_goals try (
      change [((liftPorts f).toFun (embed H (.input 0)))] = [embed H' (.input 0)]
      rw [lift_embed,input_fixed])
    all_goals
      change ((H.target e).map _).map _ = (H'.target (f.edges.toFun e)).map _
      rw [← f.target e]
      simp only [List.map_map]
      apply List.map_congr_left
      intro v _
      have law := lift_embed f v
      change (liftPorts f).toFun (insert H v) = insert H' (f.ports.toFun v)
      simpa only [insert_eq_embed] using law
end Hypernets.Copying.InstancePrefix

namespace Hypernets.Copying.Translation
open Graph
/-- Bijective resource renaming of the original atom clause, retaining its instance edge. -/
def atom_rename (d : Nat) {k h}
    (ρ : Bijection (Fin k) (Fin k)) (α : Bijection (Fin h) (Fin h)) (a : Fin h) :
    BoundaryIso (atom d k a) (atom d k (α.toFun a)) := by
  unfold atom
  exact BoundaryIso.castInterfaces _ _ _ _
    ((Distributor.boundaryIso .term 0 d ρ).tensor
      (InstancePrefix.iso (selectedResource_rename d .atom α a)))
end Hypernets.Copying.Translation

import Hypernets.Copying.ClassObservations
import Hypernets.Graph.ExpansionPeel

/-! Collapse corolla expansions and isolate a single genuine replacement. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph

theorem LabelCopy.no_internal {d I O} {G : Hypernet d I O} {label}
    (copy : LabelCopy G label) (v : G.Internal) : False := by
  obtain ⟨e,mem⟩ := (G.source_coverage (.internal v)).mpr (by simp [Port.IsOutput])
  rw [copy.only e,copy.source] at mem
  obtain ⟨i,_,eq⟩ := List.mem_map.mp mem
  cases eq

namespace FillingCollapse
variable {d I O} (C : Hypernet d I O)
    (F : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))
    (labels : C.Edge → (alphabet d).Symbol) (copies : ∀ e, LabelCopy (F e) (labels e))

def vertices : Bijection (C.expand F).Internal C.Internal where
  toFun | .inl v => v | .inr ⟨e,v⟩ => False.elim ((copies e).no_internal v)
  invFun := Sum.inl
  left_inv v := by rcases v with v | ⟨e,v⟩; rfl; exact False.elim ((copies e).no_internal v)
  right_inv _ := rfl

def edges : Bijection (C.expand F).Edge C.Edge where
  toFun := Sigma.fst
  invFun e := ⟨e,(copies e).edge⟩
  left_inv x := by obtain ⟨e,x⟩ := x; exact congrArg (Sigma.mk e) ((copies e).only x).symm
  right_inv _ := rfl

theorem source (e : C.Edge) (x : (F e).Edge) :
    ((C.expand F).source ⟨e,x⟩).map (Port.map (vertices C F labels copies).toFun) = C.source e := by
  change (((F e).source x).map (Net.Expansion.insert C F e)).map _ = _
  rw [(copies e).only x,(copies e).source,List.map_map]
  have eq : (Port.map (vertices C F labels copies).toFun ∘ Net.Expansion.insert C F e) ∘ Port.input = C.sourcePort e := by
    funext j
    change Port.map (vertices C F labels copies).toFun (Net.Expansion.host C F (C.sourcePort e j)) = _
    cases C.sourcePort e j <;> rfl
  rw [List.map_map,eq,Net.PlugUnit.sourcePort_list]

theorem target (e : C.Edge) (x : (F e).Edge) :
    ((C.expand F).target ⟨e,x⟩).map (Port.map (vertices C F labels copies).toFun) = C.target e := by
  change (((F e).target x).map (Net.Expansion.insert C F e)).map _ = _
  rw [(copies e).only x,(copies e).target,List.map_map]
  have eq : (Port.map (vertices C F labels copies).toFun ∘ Net.Expansion.insert C F e) ∘ Port.output = C.targetPort e := by
    funext j
    change Port.map (vertices C F labels copies).toFun (Net.Expansion.host C F (C.targetPort e j)) = _
    cases C.targetPort e j <;> rfl
  rw [List.map_map,eq,Net.PlugUnit.targetPort_list]

/-- A family of literal edge copies restores the original graph, including boxes. -/
def identity (copies : ∀ e, LabelCopy (F e) (C.edgeLabel e)) : Net.Iso (C.expand F) C where
  vertices := vertices C F C.edgeLabel copies
  edges := edges C F C.edgeLabel copies
  internal_label v := by rcases v with v | ⟨e,v⟩; rfl; exact False.elim ((copies e).no_internal v)
  edge_label x := by obtain ⟨e,x⟩ := x; exact ((copies e).only x ▸ (copies e).edge_label).symm
  source x := source C F C.edgeLabel copies x.1 x.2
  target x := target C F C.edgeLabel copies x.1 x.2

/-- The same collapse permits prescribed replacement labels of identical signature. -/
def relabel (input : ∀ e, (alphabet d).signature.input (labels e) = (alphabet d).signature.input (C.edgeLabel e))
    (output : ∀ e, (alphabet d).signature.output (labels e) = (alphabet d).signature.output (C.edgeLabel e)) :
    Net.Iso (C.expand F) (C.relabelEdges (alphabet d).signature labels input output) where
  vertices := vertices C F labels copies
  edges := edges C F labels copies
  internal_label v := by rcases v with v | ⟨e,v⟩; rfl; exact False.elim ((copies e).no_internal v)
  edge_label x := by obtain ⟨e,x⟩ := x; exact ((copies e).only x ▸ (copies e).edge_label).symm
  source x := source C F labels copies x.1 x.2
  target x := target C F labels copies x.1 x.2
end FillingCollapse

namespace SingleExpansion
variable {d I O} (C : Hypernet d I O) (e : C.Edge)
    (H : Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e)))

noncomputable def family (f : C.Edge) : Hypernet d ((alphabet d).signature.input (C.edgeLabel f))
    ((alphabet d).signature.output (C.edgeLabel f)) := by
  classical
  exact if eq : f = e then eq.symm ▸ H else Net.corolla (alphabet d).signature (C.edgeLabel f)

@[simp] theorem selected : family C e H e = H := by
  classical
  simp [family]

def retained (f : C.Edge) (ne : f ≠ e) : LabelCopy (family C e H f) (C.edgeLabel f) := by
  classical
  simpa only [family,dite_eq_right ne] using LabelCopy.corolla (C.edgeLabel f)

/-- Single-edge simultaneous expansion is the original plug, up to carrier names. -/
noncomputable def iso : DeepIso (C.expand (family C e H)) (C.plug e H) := by
  let F := family C e H
  have copies : ∀ x, LabelCopy (Net.ExpansionPeel.rest C F e x) ((C.plug e (F e)).edgeLabel x) := by
    intro x
    rcases x with f | x
    · exact retained C e H f.val f.property
    · exact LabelCopy.corolla _
  have f := (DeepIso.ofIso (Net.ExpansionPeel.iso C F e)).symm.trans
    (DeepIso.ofIso (FillingCollapse.identity _ _ copies))
  simpa only [F,selected] using f
end SingleExpansion
end Hypernets.Copying

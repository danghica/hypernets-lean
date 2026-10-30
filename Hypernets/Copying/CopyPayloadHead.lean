import Hypernets.Copying.CopyPayloadNormal

/-! The original copyability judgement supplies an actual nonsharing head at
the payload's sole input, independently of its chosen graph representation. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Copyable
open Graph

/-- Both plain payloads and lambdas begin with a genuine nonsharing primitive;
renaming changes neither the ordered singleton input nor this classification. -/
theorem head {d k h} {G : Hypernet d [.term] (environmentInterface k h)}
    (copyable : Copyable G) :
    ∃ e p, G.edgeLabel e = primitiveLabel d p ∧ G.source e = [.input 0] ∧
      (∀ s, p ≠ .weakening s ∧ p ≠ .contraction s) ∧ (∀ n, p ≠ .hole n) := by
  obtain ⟨H,⟨normal⟩,⟨iso⟩⟩ := CopyRule.normal_form copyable
  refine ⟨iso.edges.invFun normal.head,normal.primitive,?_,?_,?_,?_⟩
  · exact (Search.primitive_equiv (iso.symm.edge_label normal.head) _).mp normal.head_at.1
  · have source := iso.symm.source normal.head
    rw [normal.head_source] at source
    simpa only [List.map_cons,List.map_nil,Port.map,DeepIso.symm,Net.RelIso.symm,Bijection.symm] using source.symm
  · cases normal with
    | lambda B => intro s; exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
    | plain d c => cases c <;> intro s <;> exact ⟨(by intro eq; cases eq),(by intro eq; cases eq)⟩
  · cases normal with
    | lambda B => intro n eq; cases eq
    | plain d c => cases c <;> intro n eq <;> cases eq

end Hypernets.Copying.Copyable

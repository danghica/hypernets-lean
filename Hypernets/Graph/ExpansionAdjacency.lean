import Hypernets.Graph.Simultaneous
import Hypernets.Graph.Paths

/-! Exact adjacency reflection inside an expansion, and boundary crossings. -/
namespace Hypernets.Graph.Net.Expansion
universe u
variable {L : Type} {Op : Type u} {σ : Signature L Op} {I O}
    (C : Net σ I O)
    (H : (e : C.Edge) → Net σ (σ.input (C.edgeLabel e)) (σ.output (C.edgeLabel e)))

/-- Without a self-loop at the expanded edge, its whole vertex inclusion is injective. -/
theorem insert_injective (e : C.Edge) (noLoop : Replacement.NonSelfLoop C e)
    {a b : (H e).Vertex} (eq : insert C H e a = insert C H e b) : a = b := by
  cases a with
  | internal v => cases b with
    | internal w =>
      have h := Sum.inr.inj (Port.internal.inj eq)
      exact congrArg Port.internal (eq_of_heq (Sigma.mk.inj h).2)
    | input j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
    | output j => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
  | input i => cases b with
    | internal w => exact False.elim (host_ne_internal C H _ _ _ eq)
    | input j => exact congrArg Port.input (C.sourcePort_injective e (host_injective C H eq))
    | output j =>
      have same := host_injective C H eq
      exact False.elim (noLoop _ (C.sourcePort_mem e i) (same.symm ▸ C.targetPort_mem e j))
  | output i => cases b with
    | internal w => exact False.elim (host_ne_internal C H _ _ _ eq)
    | output j => exact congrArg Port.output (C.targetPort_injective e (host_injective C H eq))
    | input j =>
      have same := host_injective C H eq
      exact False.elim (noLoop _ (C.sourcePort_mem e j) (same ▸ C.targetPort_mem e i))

theorem adjacent_same_iff (e : C.Edge) (noLoop : Replacement.NonSelfLoop C e)
    (a b : (H e).Edge) :
    (C.expand H).Adjacent ⟨e,a⟩ ⟨e,b⟩ ↔ (H e).Adjacent a b := by
  constructor
  · rintro ⟨v,hv,hw⟩
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    obtain ⟨y,hy,eq⟩ := List.mem_map.mp hw
    have same := insert_injective C H e noLoop eq
    subst y
    exact ⟨x,hx,hy⟩
  · rintro ⟨v,hv,hw⟩
    exact ⟨insert C H e v,List.mem_map_of_mem hv,List.mem_map_of_mem hw⟩

/-- Any adjacency between distinct inserted components comes from an
adjacency of their old edges. Internal vertices cannot cross component tags. -/
theorem adjacent_cross {e f : C.Edge} (ne : e ≠ f) (a : (H e).Edge) (b : (H f).Edge)
    (adj : (C.expand H).Adjacent ⟨e,a⟩ ⟨f,b⟩) : C.Adjacent e f := by
  obtain ⟨v,hv,hw⟩ := adj
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
  obtain ⟨y,hy,eq⟩ := List.mem_map.mp hw
  cases x with
  | input i => exact False.elim ((H e).target_not_input hx trivial)
  | internal v => cases y with
    | output j => exact False.elim ((H f).source_not_output hy trivial)
    | internal w =>
      exact False.elim (ne (congrArg Sigma.fst (Sum.inr.inj (Port.internal.inj eq))).symm)
    | input j => exact False.elim (host_ne_internal C H _ _ _ eq)
  | output i => cases y with
    | output j => exact False.elim ((H f).source_not_output hy trivial)
    | internal w => exact False.elim (host_ne_internal C H _ _ _ eq.symm)
    | input j =>
      have same := host_injective C H eq
      exact ⟨C.targetPort e i,C.targetPort_mem e i,same ▸ C.sourcePort_mem f j⟩
end Hypernets.Graph.Net.Expansion

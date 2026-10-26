import Hypernets.Copying.Search

/-! Exact transport of copying-search steps, including changes of allowance.
Concrete boundary-isomorphism and padding instances are proved separately. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Search
open Graph

/-- The operational data needed to transport search, with all laws explicit. -/
structure Transport {d r I O J K} (G : Hypernet d I O) (H : Hypernet r J K) where
  ports : Bijection G.Vertex H.Vertex
  edges : Bijection G.Edge H.Edge
  primitive : ∀ e p, G.edgeLabel e = primitiveLabel d p ↔ H.edgeLabel (edges.toFun e) = primitiveLabel r p
  source : ∀ e, (G.source e).map ports.toFun = H.source (edges.toFun e)
  target : ∀ e, (G.target e).map ports.toFun = H.target (edges.toFun e)
  input_iff : ∀ v, (ports.toFun v).IsInput ↔ v.IsInput

namespace Transport
variable {d r I O J K} {G : Hypernet d I O} {H : Hypernet r J K}

def positions (f : Transport G H) : Bijection (Position G) (Position H) where
  toFun s := (s.1,f.ports.toFun s.2)
  invFun t := (t.1,f.ports.invFun t.2)
  left_inv s := by rcases s with ⟨m,v⟩; simp [f.ports.left_inv]
  right_inv t := by rcases t with ⟨m,v⟩; simp [f.ports.right_inv]

def symm (f : Transport G H) : Transport H G where
  ports := f.ports.symm
  edges := f.edges.symm
  primitive e p := by simpa [Bijection.symm,f.edges.right_inv] using (f.primitive (f.edges.invFun e) p).symm
  source e := by
    have eq := congrArg (List.map f.ports.invFun) (f.source (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.ports.left_inv,f.edges.right_inv,Bijection.symm] using eq.symm
  target e := by
    have eq := congrArg (List.map f.ports.invFun) (f.target (f.edges.invFun e))
    simpa [List.map_map,Function.comp_def,f.ports.left_inv,f.edges.right_inv,Bijection.symm] using eq.symm
  input_iff v := by simpa [Bijection.symm,f.ports.right_inv] using (f.input_iff (f.ports.invFun v)).symm

/-- Every witnessed interaction transports with the same operation and argument number. -/
theorem step (f : Transport G H) {s t} (a : Step G s t) :
    Step H (f.positions.toFun s) (f.positions.toFun t) := by
  cases a with
  | search e p v t label src result =>
    apply Step.search (f.edges.toFun e) p _ _ ((f.primitive e p).mp label)
    · rw [← f.source]; exact List.mem_map_of_mem src
    · rw [← f.target,enter_map,result]; rfl
  | backtrack e o root v i t label src bound arg result =>
    apply Step.backtrack (f.edges.toFun e) o (f.ports.toFun root) _ i _ ((f.primitive e _).mp label)
    · rw [← f.source,src]; rfl
    · exact bound
    · rw [← f.target,List.getElem?_map,arg]; rfl
    · rw [← f.target,resume_map,result]; rfl

/-- Reflection rules out extra search behaviour in a transported representation. -/
theorem step_iff (f : Transport G H) (s t : Position G) :
    Step H (f.positions.toFun s) (f.positions.toFun t) ↔ Step G s t := by
  constructor
  · intro a
    have b := f.symm.step a
    simpa [positions,symm,Bijection.symm,f.ports.left_inv] using b
  · exact f.step

theorem trace_iff (f : Transport G H) (s t : Position G) (n : Nat) :
    Trace (Step H) (f.positions.toFun s) (f.positions.toFun t) n ↔ Trace (Step G) s t n :=
  Trace.map_iff f.positions f.step_iff s t n

theorem terminal_iff (f : Transport G H) (s : Position G) :
    Terminal (Step H) (f.positions.toFun s) ↔ Terminal (Step G) s := by
  constructor
  · intro h t a; exact h _ (f.step a)
  · intro h t a
    have b := f.symm.step a
    have bad := h (f.positions.invFun t)
    apply bad
    simpa [positions,symm,Bijection.symm,f.ports.left_inv] using b
end Transport

/-- Recursive label equivalence agrees literally on every primitive interaction. -/
theorem primitive_equiv {d} {a b : (alphabet d).Symbol} (rel : LabelEquiv d a b) (p : Primitive) :
    a = primitiveLabel d p ↔ b = primitiveLabel d p := by
  cases d with
  | zero => rw [rel]
  | succ d =>
    cases a with
    | inl a => cases b with
      | inl b => change a = b at rel; subst b; rfl
      | inr b => exact False.elim rel
    | inr a => cases b with
      | inl b => exact False.elim rel
      | inr b => simp [primitiveLabel]

/-- Actual typed boundary isomorphisms satisfy every operational transport law. -/
def ofBoundaryIso {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (f : BoundaryIso G H) : Transport G H where
  ports := f.ports
  edges := f.edges
  primitive e p := primitive_equiv (f.edge_label e) p
  source := f.source
  target := f.target
  input_iff := f.input_iff
end Hypernets.Copying.Search

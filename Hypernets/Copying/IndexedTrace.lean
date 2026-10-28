import Hypernets.Graph.FiniteTrace

/-! Exact finite traces expose their ordered positions without choosing an
unrelated path presentation. Prefix and suffix lengths are retained. -/
namespace Hypernets.Graph.Trace

/-- An n-step trace has n+1 indexed positions, exact endpoints, adjacent
successors, and exact prefix and suffix traces at every position. -/
theorem indexed {α : Type} {R : α → α → Prop} {a b : α} {n : Nat}
    (path : Trace R a b n) :
    ∃ f : Fin (n+1) → α,
      f ⟨0,by omega⟩ = a ∧ f ⟨n,by omega⟩ = b ∧
      (∀ i : Fin n, R (f i.castSucc) (f i.succ)) ∧
      (∀ i, Trace R a (f i) i.val) ∧
      (∀ i, Trace R (f i) b (n-i.val)) := by
  induction path with
  | refl a =>
    refine ⟨fun _ => a,rfl,rfl,fun i => Fin.elim0 i,?_,?_⟩
    · intro i
      have z : i.val = 0 := by omega
      simpa [z] using Trace.refl (R := R) a
    · intro i; simpa using Trace.refl (R := R) a
  | @step a c b n hop path ih =>
    obtain ⟨g,first,last,adj,pre,suffix⟩ := ih
    let f : Fin (n+1+1) → α := Fin.cases a g
    refine ⟨f,rfl,?_,?_,?_,?_⟩
    · change g ⟨n,by omega⟩ = b
      exact last
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change R a (g 0)
        rw [show g 0 = c from first]
        exact hop
      · change R (g j.castSucc) (g j.succ)
        exact adj j
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact .refl _
      · change Trace R a (g j) (j.val+1)
        exact .step hop (pre j)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · change Trace R a b (n+1-0)
        exact .step hop path
      · change Trace R (g j) b (n+1-(j.val+1))
        simpa using suffix j

/-- If forward steps are functional and the last vertex is terminal, distinct
positions of a successful trace cannot denote the same vertex. -/
theorem indexed_injective {α : Type} {R : α → α → Prop} {b : α} {n : Nat}
    (functional : ∀ {a b c}, R a b → R a c → b = c)
    (terminal : Terminal R b) (f : Fin (n+1) → α)
    (suffix : ∀ i, Trace R (f i) b (n-i.val)) : Function.Injective f := by
  intro i j eq
  have len := (Trace.terminal_unique (R := R) (fun h h' => functional h h') (suffix i) (eq ▸ suffix j) terminal terminal).2
  apply Fin.ext
  omega

end Hypernets.Graph.Trace

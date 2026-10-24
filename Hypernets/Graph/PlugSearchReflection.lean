import Hypernets.Graph.RootedCoordinates

/-! Exact search reflection for one arbitrary shallow filling. -/
namespace Hypernets.Linear.PlugSearchReflection
open Graph Net.Replacement
variable {Op : Type} {ops : Operations Op} {d : Nat} {I O : List Wire}
variable (C : Hypernet ops d I O) (hole : C.Edge)
    (H : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel hole))
      ((alphabet ops d).signature.output (C.edgeLabel hole)))

/-- Carry a coordinate by the retained host-vertex injection. -/
def position (p : SearchPosition C) : SearchPosition (C.plug hole H) :=
  p.map id (host C hole H)

/-- A retained operation has exactly its original operational data. -/
theorem operation_readback (a : SearchOperation (C.plug hole H))
    (e : {e : C.Edge // e ≠ hole}) (edge : a.edge = .inl e) :
    ∃ b : SearchOperation C, b.edge = e.val ∧
      a.source = host C hole H b.source ∧ a.arguments = b.arguments.map (host C hole H) := by
  have label : C.edgeLabel e.val = primitiveLabel ops d (.operation a.operation) := by
    have h := a.label; rw [edge] at h; exact h
  obtain ⟨b,be,_⟩ := SearchOperation.exists_view e.val a.operation label
  have ne : b.edge ≠ hole := be ▸ e.property
  have same : a.edge = (b.plug hole ne H).edge := by rw [edge]; exact congrArg Sum.inl (Subtype.ext be.symm)
  have data := a.data_unique (b.plug hole ne H) same
  exact ⟨b,be,data.2.1,data.2.2⟩

/-- The only obstruction to reflection is a mode-sensitive boundary of the filled edge. -/
def Boundary (p : SearchPosition C) : Prop :=
  (p.1 = .search ∧ p.2 ∈ C.source hole) ∨ (p.1 = .backtrack ∧ p.2 ∈ C.target hole)

/-- An inserted edge can meet a host source only at an input of the filling. -/
theorem source_boundary {e : H.Edge} {v : C.Vertex}
    (mem : host C hole H v ∈ (C.plug hole H).source (.inr e)) : v ∈ C.source hole := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  obtain ⟨i,_,same⟩ := insert_source_host C hole H (H.source_not_output hw) eq
  exact same ▸ C.sourcePort_mem hole i

/-- An inserted edge can meet a host target only at an output of the filling. -/
theorem target_boundary {e : H.Edge} {v : C.Vertex}
    (mem : host C hole H v ∈ (C.plug hole H).target (.inr e)) : v ∈ C.target hole := by
  obtain ⟨w,hw,eq⟩ := List.mem_map.mp mem
  obtain ⟨i,_,same⟩ := insert_target_host C hole H (H.target_not_input hw) eq
  exact same ▸ C.targetPort_mem hole i

/-- Search reflects to the original context away from the filled edge's boundary. -/
theorem reflect {kind : Op → OperationKind} (name : Hole)
    (label : C.edgeLabel hole = primitiveLabel ops d (.hole name))
    {p q} (step : SearchStep (C.plug hole H) kind (position C hole H p) q)
    (away : ¬ Boundary C hole p) :
    ∃ r, SearchStep C kind p r ∧ q = position C hole H r := by
  have finish (r) (original : SearchStep C kind p r) :
      ∃ r, SearchStep C kind p r ∧ q = position C hole H r :=
    ⟨r,original,SearchStep.deterministic step (original.plug hole name label H)⟩
  generalize hp : position C hole H p = start at step
  cases step with
  | trigger e v el source =>
      cases e with
      | inl e =>
          have mem : p.2 ∈ C.source e.val := by
            have h : host C hole H p.2 ∈ (C.source e.val).map (host C hole H) := by
              change host C hole H p.2 ∈ (C.plug hole H).source (.inl e)
              rw [source, (Prod.mk.inj hp).2]; simp
            obtain ⟨w,hw,eq⟩ := List.mem_map.mp h
            exact host_injective C hole H eq ▸ hw
          have len : (C.source e.val).length = 1 := by
            rw [C.source_length]; change ((alphabet ops d).signature.input (C.edgeLabel e.val)).length = 1
            change C.edgeLabel e.val = _ at el
            rw [el]; cases d <;> rfl
          obtain ⟨w,src⟩ := List.length_eq_one_iff.mp len
          have eq : p.2 = w := List.mem_singleton.mp (src ▸ mem)
          apply finish (.rewrite,p.2)
          have pm : p = (.search,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
          rw [pm]
          exact .trigger e.val p.2 el (src.trans (congrArg List.singleton eq.symm))
      | inr e =>
          apply False.elim (away (.inl ⟨(Prod.mk.inj hp).1,?_⟩))
          apply source_boundary C hole H
          rw [source,(Prod.mk.inj hp).2]; simp
  | enter a =>
      cases edge : a.edge with
      | inl e =>
          obtain ⟨b,be,src,_⟩ := operation_readback C hole H a e edge
          have same := host_injective C hole H ((Prod.mk.inj hp).2.trans src)
          have eq : p = (.search,b.source) := Prod.ext (Prod.mk.inj hp).1 same
          apply finish (b.enter kind)
          rw [eq]; exact .enter b
      | inr e =>
          apply False.elim (away (.inl ⟨(Prod.mk.inj hp).1,?_⟩))
          apply source_boundary C hole H
          rw [← edge,a.source_eq,(Prod.mk.inj hp).2]; simp
  | resume a i v arg =>
      cases edge : a.edge with
      | inl e =>
          obtain ⟨b,be,_,args⟩ := operation_readback C hole H a e edge
          have mapped : (b.arguments[i]?).map (host C hole H) = (some p.2).map (host C hole H) := by
            rw [← List.getElem?_map,← args,arg]
            exact congrArg some (Prod.mk.inj hp).2.symm
          have original := Option.map_injective (fun _ _ h => host_injective C hole H h) mapped
          apply finish (b.resume kind i)
          have eq : p = (.backtrack,p.2) := Prod.ext (Prod.mk.inj hp).1 rfl
          rw [eq]; exact .resume b i p.2 original
      | inr e =>
          apply False.elim (away (.inr ⟨(Prod.mk.inj hp).1,?_⟩))
          apply target_boundary C hole H
          rw [← edge,(Prod.mk.inj hp).2]
          exact a.argument_mem (List.mem_of_getElem? arg)
end Hypernets.Linear.PlugSearchReflection

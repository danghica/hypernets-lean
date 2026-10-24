import Hypernets.Graph.DeepSpecimens

/-! Finite, aligned substitution tuples read only at original hole occurrences. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

/-- One aligned entry of the two substitution vectors, with its hole signature. -/
structure TupleEntry (ops : Operations Op) where
  depth : Nat
  input : List Wire
  output : List Wire
  hole : Hole
  input_eq : input = hole.input
  output_eq : output = hole.output
  left : Hypernet ops depth input output
  right : Hypernet ops depth input output

/-- Record the two graphs assigned to an actual primitive hole. -/
def TupleEntry.at {d I O} (C : Hypernet ops d I O) (e : C.Edge)
    (h : Hole) (label : C.edgeLabel e = primitiveLabel ops d (.hole h))
    (H K : Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) : TupleEntry ops where
  depth := d
  input := (alphabet ops d).signature.input (C.edgeLabel e)
  output := (alphabet ops d).signature.output (C.edgeLabel e)
  hole := h
  input_eq := by rw [label]; cases d <;> rfl
  output_eq := by rw [label]; cases d <;> rfl
  left := H
  right := K

/-- The pointwise pre-template condition for a tuple entry. -/
def TupleEntry.Related (T : LayeredPreTemplate ops) (a : TupleEntry ops) : Prop :=
  (T a.depth).Rel a.left a.right

/-- Remove repeated enumeration entries without changing membership. -/
noncomputable def tupleDistinct {α : Type} : List α → List α
  | [] => []
  | a :: xs => by
      classical
      exact if a ∈ tupleDistinct xs then tupleDistinct xs else a :: tupleDistinct xs

theorem mem_tupleDistinct {α : Type} (a : α) (xs : List α) :
    a ∈ tupleDistinct xs ↔ a ∈ xs := by
  classical
  induction xs generalizing a with
  | nil => simp [tupleDistinct]
  | cons b xs ih =>
      simp only [tupleDistinct]
      split
      · rename_i h
        rw [ih a]
        simp only [List.mem_cons]
        exact ⟨Or.inr,fun h' => h'.elim (fun eq => eq ▸ ((ih b).mp h)) id⟩
      · simp [ih a]

theorem tupleDistinct_nodup {α : Type} (xs : List α) : (tupleDistinct xs).Nodup := by
  classical
  induction xs with
  | nil => exact .nil
  | cons a xs ih =>
      simp only [tupleDistinct]
      split
      · exact ih
      · exact List.nodup_cons.mpr ⟨by assumption,ih⟩

/-- Enumerate shallow edges once, regardless of duplicates in the supplied enumeration. -/
noncomputable def tupleEdges {d I O} (C : Hypernet ops d I O) : List C.Edge :=
  tupleDistinct C.finiteEdge.elements

theorem mem_tupleEdges {d I O} (C : Hypernet ops d I O) (e : C.Edge) : e ∈ tupleEdges C :=
  (mem_tupleDistinct e _).mpr (C.finiteEdge.complete e)

mutual
/-- Tuple application traverses original edges and original box bodies. Hole
replacement is a leaf: inserted graphs are never recursively substituted. The
list records both replacement vectors in the same traversal order. -/
inductive TupleFilling (T : LayeredPreTemplate ops) : {d : Nat} → {I O : List Wire} →
    Hypernet ops d I O → Hypernet ops d I O → Hypernet ops d I O → List (TupleEntry ops) → Prop where
  | expand {d I O} (C : Hypernet ops d I O)
      (H K : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
        ((alphabet ops d).signature.output (C.edgeLabel e)))
      (entries : C.Edge → List (TupleEntry ops))
      (edges : ∀ e, TupleFillingEdge T C H K e (entries e)) :
      TupleFilling T C (C.expand H) (C.expand K) ((tupleEdges C).flatMap entries)

/-- The local clauses of simultaneous original-hole tuple application. -/
inductive TupleFillingEdge (T : LayeredPreTemplate ops) : {d : Nat} → {I O : List Wire} →
    (C : Hypernet ops d I O) →
    ((e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) →
    ((e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e))) → C.Edge → List (TupleEntry ops) → Prop where
  | retained {d I O C H K e} :
      ExpansionPaths.CorollaCopy (ops := ops) (d := d) (I := I) (O := O) C H e →
      ExpansionPaths.CorollaCopy C K e → TupleFillingEdge T C H K e []
  | filled {d I O C H K e} (h : Hole)
      (label : C.edgeLabel e = primitiveLabel ops d (.hole h))
      (rel : (T d).Rel (H e) (K e)) :
      TupleFillingEdge T (I := I) (O := O) C H K e [TupleEntry.at C e h label (H e) (K e)]
  | boxed {d I O} {C : Hypernet ops (d+1) I O} {H K e}
      (b : Box (alphabet ops d)) (label : C.edgeLabel e = .inr b)
      {L R : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term)}
      {entries : List (TupleEntry ops)} (inner : TupleFilling T b.body L R entries)
      (left : LabelCopy (ops := ops) (d := d+1) (H e) (.inr ⟨b.bound,b.free,L⟩))
      (right : LabelCopy (ops := ops) (d := d+1) (K e) (.inr ⟨b.bound,b.free,R⟩)) :
      TupleFillingEdge T C H K e entries
end

/-- Erasing the finite tuple recovers exactly the previous recursive certificate. -/
theorem TupleFilling.forget {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries) :
    DeepFilling T C L R := by
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K entries edges =>
          apply DeepFilling.expand C H K
          intro e
          have cert := edges e
          generalize entries e = xs at cert
          cases cert with
          | retained l r => exact .retained l r
          | filled h label rel => exact .filled h label rel
  | succ d ih =>
      cases f with
      | expand C H K entries edges =>
          apply DeepFilling.expand C H K
          intro e
          have cert := edges e
          generalize entries e = xs at cert
          cases cert with
          | retained l r => exact .retained l r
          | filled h label rel => exact .filled h label rel
          | boxed b label inner l r => exact .boxed b label (ih inner) l r

/-- Every recursive certificate yields finite, equally long substitution vectors. -/
theorem DeepFilling.tuple {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} (f : DeepFilling T C L R) :
    ∃ entries, TupleFilling T C L R entries := by
  classical
  induction d generalizing I O with
  | zero =>
      cases f with
      | expand C H K edges =>
          have localTuple (e : C.Edge) : ∃ es, TupleFillingEdge T C H K e es := by
            cases edges e with
            | retained l r => exact ⟨[],.retained l r⟩
            | filled h label rel => exact ⟨_,.filled h label rel⟩
          exact ⟨_,.expand C H K (fun e => (localTuple e).choose) (fun e => (localTuple e).choose_spec)⟩
  | succ d ih =>
      cases f with
      | expand C H K edges =>
          have localTuple (e : C.Edge) : ∃ es, TupleFillingEdge T C H K e es := by
            cases edges e with
            | retained l r => exact ⟨[],.retained l r⟩
            | filled h label rel => exact ⟨_,.filled h label rel⟩
            | boxed b label inner l r =>
                obtain ⟨es,run⟩ := ih inner
                exact ⟨es,.boxed b label run l r⟩
          exact ⟨_,.expand C H K (fun e => (localTuple e).choose) (fun e => (localTuple e).choose_spec)⟩

/-- Tuple application and recursive filling have exactly the same endpoints. -/
theorem tupleFilling_iff {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} :
    (∃ entries, TupleFilling T C L R entries) ↔ DeepFilling T C L R :=
  ⟨fun ⟨_,f⟩ => f.forget,DeepFilling.tuple⟩

/-- Every recorded pair satisfies the original pointwise relation. -/
theorem TupleFilling.related {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries) :
    ∀ a ∈ entries, a.Related T := by
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              exact rel
  | succ d ih =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              exact rel
          | boxed b label inner l r => exact ih inner a mem

/-- Every tuple entry names a hole in the original graph, at its original depth. -/
theorem TupleFilling.provenance {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries) :
    ∀ a ∈ entries, HasHole C a.hole := by
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              exact ⟨e,by change primitiveHole (C.edgeLabel e).down = _; rw [label]; rfl⟩
  | succ d ih =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          apply (hasHole_partition C e a.hole).mpr
          right
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              change ∃ x, fiberHole ops (d+1) (C.edgeLabel e) x = some h
              rw [label]
              exact ⟨.inl (),rfl⟩
          | boxed b label inner l r =>
              exact (edgeHasHole_box C e b label a.hole).mpr (ih inner a mem)

/-- Local provenance retains the owning original edge, including enclosing boxes. -/
theorem TupleFillingEdge.provenance {T : LayeredPreTemplate ops} {d I O}
    {C : Hypernet ops d I O} {H K e entries} (f : TupleFillingEdge T C H K e entries) :
    ∀ a ∈ entries, EdgeHasHole C e a.hole := by
  intro a mem
  cases f with
  | retained l r => cases mem
  | filled h label rel =>
      have eq := List.mem_singleton.mp mem
      subst a
      unfold EdgeHasHole
      rw [label]
      exact ⟨.inl (),by cases d <;> rfl⟩
  | boxed b label inner l r =>
      exact (edgeHasHole_box C e b label a.hole).mpr (inner.provenance a mem)

/-- In a unique-hole context the recorded hole names are pairwise distinct. -/
theorem TupleFilling.unique {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries)
    (unique : UniqueHoles ops d C) : (entries.map TupleEntry.hole).Nodup := by
  have across {d I O} {C : Hypernet ops d I O} {H K} {es : C.Edge → List (TupleEntry ops)}
      (edges : ∀ e, TupleFillingEdge T C H K e (es e))
      (unique : UniqueHoles ops d C) {e g : C.Edge} (ne : e ≠ g)
      {a b : TupleEntry ops} (ha : a ∈ es e) (hb : b ∈ es g) : a.hole ≠ b.hole := by
    intro eq
    obtain ⟨x,hx⟩ := (edges e).provenance a ha
    obtain ⟨y,hy⟩ := (edges g).provenance b hb
    have same := (uniqueHoles_iff_occurrences C).mp unique b.hole ⟨e,x⟩ ⟨g,y⟩ (by simpa [occurrenceHole,eq] using hx) hy
    exact ne (congrArg Sigma.fst same)
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K es edges =>
          rw [List.Nodup,List.pairwise_map,List.pairwise_flatMap]
          constructor
          · intro e _
            have cert := edges e
            generalize es e = xs at cert ⊢
            cases cert with
            | retained l r => exact .nil
            | filled h label rel => exact .cons (by simp) .nil
          · exact (tupleDistinct_nodup C.finiteEdge.elements).imp_of_mem
              (fun _ _ ne a ha b hb => across edges unique ne ha hb)
  | succ d ih =>
      cases f with
      | expand C H K es edges =>
          rw [List.Nodup,List.pairwise_map,List.pairwise_flatMap]
          constructor
          · intro e _
            have cert := edges e
            generalize es e = xs at cert ⊢
            cases cert with
            | retained l r => exact .nil
            | filled h label rel => exact .cons (by simp) .nil
            | boxed b label inner l r =>
                exact List.pairwise_map.mp (ih inner (uniqueHoles_box_body C e b label unique))
          · exact (tupleDistinct_nodup C.finiteEdge.elements).imp_of_mem
              (fun _ _ ne a ha b hb => across edges unique ne ha hb)

/-- Hole freedom of an expansion reflects to every inserted graph. -/
theorem tuple_component_closed {d I O} (C : Hypernet ops d I O)
    (H : (e : C.Edge) → Hypernet ops d ((alphabet ops d).signature.input (C.edgeLabel e))
      ((alphabet ops d).signature.output (C.edgeLabel e)))
    (closed : HoleFree (C.expand H)) (e : C.Edge) : HoleFree (H e) := by
  intro h present
  obtain ⟨⟨x,p⟩,hp⟩ := (hasHole_iff_occurrences (H e) h).mp present
  exact closed h ((hasHole_iff_occurrences (C.expand H) h).mpr ⟨⟨⟨e,x⟩,p⟩,hp⟩)

/-- A closed one-edge copy of a box has a closed body. -/
theorem LabelCopy.body_closed {d I O} {G : Hypernet ops (d+1) I O}
    {b : Box (alphabet ops d)} (copy : LabelCopy G (.inr b))
    (closed : HoleFree G) : HoleFree b.body := by
  intro h present
  exact closed h ((hasHole_partition G copy.edge h).mpr
    (.inr ((edgeHasHole_box G copy.edge b copy.edge_label h).mpr present)))

/-- A closed result forces every original hole to occur in the substitution tuple. -/
theorem TupleFilling.complete {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries)
    (closed : HoleFree L) : ∀ h, HasHole C h → ∃ a ∈ entries, a.hole = h := by
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K es edges =>
          intro h present
          obtain ⟨⟨e,p⟩,hp⟩ := (hasHole_iff_occurrences C h).mp present
          have cert := edges e
          have localClosed := tuple_component_closed C H closed e
          have witness : ∃ a ∈ es e, a.hole = h := by
            generalize es e = xs at cert ⊢
            cases cert with
            | retained l r =>
                apply False.elim
                apply localClosed h
                apply (hasHole_iff_occurrences (H e) h).mpr
                exact ⟨⟨l.edge,l.label.symm ▸ p⟩,(fiberHole_transport l.label.symm p).trans hp⟩
            | filled h' label rel =>
                have same : h' = h := by
                  change fiberHole ops 0 (C.edgeLabel e) p = some h at hp
                  have transported := (fiberHole_transport label p).trans hp
                  generalize label ▸ p = q at transported
                  cases q with
                  | inl u => exact Option.some.inj transported
                  | inr bad => exact nomatch bad
                exact ⟨TupleEntry.at C e h' label (H e) (K e),List.mem_singleton.mpr rfl,same⟩
          obtain ⟨a,mem,eq⟩ := witness
          exact ⟨a,List.mem_flatMap.mpr ⟨e,mem_tupleEdges C e,mem⟩,eq⟩
  | succ d ih =>
      cases f with
      | expand C H K es edges =>
          intro h present
          obtain ⟨⟨e,p⟩,hp⟩ := (hasHole_iff_occurrences C h).mp present
          have cert := edges e
          have localClosed := tuple_component_closed C H closed e
          have witness : ∃ a ∈ es e, a.hole = h := by
            generalize es e = xs at cert ⊢
            cases cert with
            | retained l r =>
                apply False.elim
                apply localClosed h
                apply (hasHole_iff_occurrences (H e) h).mpr
                exact ⟨⟨l.edge,l.label.symm ▸ p⟩,(fiberHole_transport l.label.symm p).trans hp⟩
            | filled h' label rel =>
                have same : h' = h := by
                  change fiberHole ops (d+1) (C.edgeLabel e) p = some h at hp
                  have transported := (fiberHole_transport label p).trans hp
                  generalize label ▸ p = q at transported
                  cases q with
                  | inl u => exact Option.some.inj transported
                  | inr bad => exact nomatch bad
                exact ⟨TupleEntry.at C e h' label (H e) (K e),List.mem_singleton.mpr rfl,same⟩
            | boxed b label inner l r =>
                exact ih inner (l.body_closed localClosed) h
                  ((edgeHasHole_box C e b label h).mp ⟨p,hp⟩)
          obtain ⟨a,mem,eq⟩ := witness
          exact ⟨a,List.mem_flatMap.mpr ⟨e,mem_tupleEdges C e,mem⟩,eq⟩

/-- On a context with a closed filled result, tuple names enumerate exactly its
original holes, once each. This excludes both omitted and invented variables. -/
theorem TupleFilling.inventory {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries)
    (unique : UniqueHoles ops d C) (closed : HoleFree L) :
    (entries.map TupleEntry.hole).Nodup ∧
      ∀ h, h ∈ entries.map TupleEntry.hole ↔ HasHole C h := by
  refine ⟨f.unique unique,?_⟩
  intro h
  constructor
  · intro mem
    obtain ⟨a,amem,eq⟩ := List.mem_map.mp mem
    rw [← eq]
    exact f.provenance a amem
  · intro present
    obtain ⟨a,mem,eq⟩ := f.complete closed h present
    exact List.mem_map.mpr ⟨a,mem,eq⟩

/-- Every actual recursive specimen has a finite original-hole tuple with the
same two filled graphs and pointwise related entries, exhausting its holes. -/
theorem DeepSpecimen.tuple {T : LayeredPreTemplate ops} {d}
    {Allowed : Hypernet ops d [.term] [] → Prop} (S : DeepSpecimen T Allowed) :
    ∃ entries, TupleFilling T S.context.val S.leftState.graph S.rightState.graph entries ∧
      (∀ a ∈ entries, a.Related T) ∧ (entries.map TupleEntry.hole).Nodup ∧
      (∀ h, h ∈ entries.map TupleEntry.hole ↔ HasHole S.context.val h) := by
  obtain ⟨es,run⟩ := S.filling.tuple
  exact ⟨es,run,run.related,(run.inventory S.context.property S.left_closed).1,
    (run.inventory S.context.property S.left_closed).2⟩

/-- Both graphs in every tuple entry are closed whenever both filled results are. -/
theorem TupleFilling.entries_closed {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {entries} (f : TupleFilling T C L R entries)
    (lc : HoleFree L) (rc : HoleFree R) :
    ∀ a ∈ entries, HoleFree a.left ∧ HoleFree a.right := by
  induction d generalizing I O entries with
  | zero =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              exact ⟨tuple_component_closed C H lc e,tuple_component_closed C K rc e⟩
  | succ d ih =>
      cases f with
      | expand C H K es edges =>
          intro a mem
          obtain ⟨e,_,mem⟩ := List.mem_flatMap.mp mem
          have cert := edges e
          generalize es e = xs at cert mem
          cases cert with
          | retained l r => cases mem
          | filled h label rel =>
              have eq := List.mem_singleton.mp mem
              subst a
              exact ⟨tuple_component_closed C H lc e,tuple_component_closed C K rc e⟩
          | boxed b label inner l r =>
              exact ih inner (l.body_closed (tuple_component_closed C H lc e))
                (r.body_closed (tuple_component_closed C K rc e)) a mem

/-- Tuple ordering is a choice of notation: any permutation of a traversal
vector applies to the same original named holes and has the same result. -/
def AppliesTuple (T : LayeredPreTemplate ops) {d I O}
    (C L R : Hypernet ops d I O) (entries : List (TupleEntry ops)) : Prop :=
  ∃ ordered, ordered.Perm entries ∧ TupleFilling T C L R ordered

/-- Recursive filling and finite named-tuple application agree in both directions. -/
theorem appliesTuple_iff {T : LayeredPreTemplate ops} {d I O} {C L R : Hypernet ops d I O} :
    (∃ entries, AppliesTuple T C L R entries) ↔ DeepFilling T C L R := by
  constructor
  · rintro ⟨_,_,_,run⟩; exact run.forget
  · intro run
    obtain ⟨es,f⟩ := run.tuple
    exact ⟨es,es,List.Perm.refl es,f⟩

/-- Reordering both replacement vectors together preserves tuple application. -/
theorem AppliesTuple.permute {T : LayeredPreTemplate ops} {d I O}
    {C L R : Hypernet ops d I O} {es fs} (f : AppliesTuple T C L R es)
    (perm : es.Perm fs) : AppliesTuple T C L R fs := by
  obtain ⟨xs,p,run⟩ := f
  exact ⟨xs,p.trans perm,run⟩

/-- A single finite tuple packages the paper's three equally long vectors. -/
structure SpecimenTuple {T : LayeredPreTemplate ops} {d}
    {Allowed : Hypernet ops d [.term] [] → Prop} (S : DeepSpecimen T Allowed) where
  entries : List (TupleEntry ops)
  applies : AppliesTuple T S.context.val S.leftState.graph S.rightState.graph entries
  related : ∀ a ∈ entries, a.Related T
  closed : ∀ a ∈ entries, HoleFree a.left ∧ HoleFree a.right
  unique : (entries.map TupleEntry.hole).Nodup
  complete : ∀ h, h ∈ entries.map TupleEntry.hole ↔ HasHole S.context.val h

/-- Every recursive specimen admits a complete, distinct named substitution tuple. -/
noncomputable def DeepSpecimen.substitutionTuple {T : LayeredPreTemplate ops} {d}
    {Allowed : Hypernet ops d [.term] [] → Prop} (S : DeepSpecimen T Allowed) : SpecimenTuple S := by
  let es := S.tuple.choose
  have spec := S.tuple.choose_spec
  exact ⟨es,⟨es,List.Perm.refl es,spec.1⟩,spec.2.1,
    spec.1.entries_closed S.left_closed S.right_closed,spec.2.2.1,spec.2.2.2⟩

/-- Forget a local tuple annotation, including recursively annotated box bodies. -/
theorem TupleFillingEdge.forget {T : LayeredPreTemplate ops} {d I O}
    {C : Hypernet ops d I O} {H K e entries} (f : TupleFillingEdge T C H K e entries) :
    DeepFillingEdge T C H K e := by
  cases f with
  | retained l r => exact .retained l r
  | filled h label rel => exact .filled h label rel
  | boxed b label inner l r => exact .boxed b label inner.forget l r

/-- Conversely, a tuple application to an allowed focussed context with closed
results constructs an actual recursive specimen with exactly those graphs. -/
theorem TupleFilling.specimen {T : LayeredPreTemplate ops} {d}
    {Allowed : Hypernet ops d [.term] [] → Prop}
    (C : Context ops d [.term] []) (focus : Focussed C.val) (allowed : Allowed focus.underlying)
    {L R : Hypernet ops d [.term] []} {entries} (run : TupleFilling T C.val L R entries)
    (lc : HoleFree L) (rc : HoleFree R) :
    ∃ S : DeepSpecimen T Allowed, S.context = C ∧ S.focus.mode = focus.mode ∧
      S.leftState.graph = L ∧ S.rightState.graph = R := by
  rcases C with ⟨C,unique⟩
  cases run with
  | expand C H K es edges =>
      let S : DeepSpecimen T Allowed := {
        context := ⟨C,unique⟩
        focus := focus
        allowed := allowed
        left := H
        right := K
        edges e := (edges e).forget
        left_closed := lc
        right_closed := rc }
      exact ⟨S,rfl,rfl,rfl,rfl⟩
end Hypernets.Linear

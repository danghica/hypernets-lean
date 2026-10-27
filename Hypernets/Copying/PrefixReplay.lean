import Hypernets.Copying.RefocusingExamples

/-! Search-prefix replay through partial retained occurrences, including deleting rewrites. -/
namespace Hypernets.Copying.Search
open Graph

/-- Only these primitives can participate in a search interaction. -/
def Interactive (p : Primitive) : Prop :=
  p = .instanceEdge ∨ p = .contraction .term ∨ ∃ o, p = .operation o

theorem enter_interactive {V : Type} {p : Primitive} {v : V} {xs q}
    (h : enter p v xs = some q) : Interactive p := by
  cases p with
  | operation o => exact .inr (.inr ⟨o,rfl⟩)
  | instanceEdge => exact .inl rfl
  | contraction s => cases s with
    | term => exact .inr (.inl rfl)
    | atom => cases h
  | weakening s => cases h
  | store => cases h
  | hole boundary => cases h
  | focus m => cases h

/-- The source or ordered return incidence used by an interaction. -/
def Uses {d I O} (G : Hypernet d I O) (p : Position G) (e : G.Edge) : Prop :=
  (p.1 = .search ∧ p.2 ∈ G.source e) ∨
  (p.1 = .backtrack ∧ ∃ j : Nat, (G.target e)[j]? = some p.2)

def mapPosition {V W : Type} (f : V → W) (p : Focus × V) : Focus × W := (p.1,f p.2)

/-- An interacting edge's source was searched earlier in the same rooted run. -/
theorem uses_visit {d I O} {G : Hypernet d I O} {i n p e v}
    (hist : History G i n p) (source : G.source e = [v]) (used : Uses G p e) :
    Visit G i n p v := by
  rcases used with ⟨mode,mem⟩ | ⟨mode,j,arg⟩
  · have eq : p.2 = v := by simpa [source] using mem
    exact eq ▸ hist.2
  · exact (hist.1.parent source (List.mem_of_getElem? arg)).2

/-- A used singleton-source edge has its source on the current history stack. -/
theorem uses_stack {d I O} {G : Hypernet d I O} {i n p e v}
    (hist : History G i n p) (source : G.source e = [v]) (used : Uses G p e) :
    HistoryStack G i (Visit G i n p) v := by
  rcases used with ⟨mode,mem⟩ | ⟨mode,j,arg⟩
  · have eq : p.2 = v := by simpa [source] using mem
    exact eq ▸ hist.1
  · exact (hist.1.parent source (List.mem_of_getElem? arg)).1

/-- Using an immediate child of an operation entails a previous visit to its parent. -/
theorem uses_parent_visit {d I O} {G : Hypernet d I O} {i n p e u head v}
    (hist : History G i n p) (source : G.source e = [u]) (used : Uses G p e)
    (parent : G.source head = [v]) (child : u ∈ G.target head) : Visit G i n p v :=
  ((uses_stack hist source used).parent parent child).2

/-- Stores never participate in pure search interactions. -/
theorem Interactive.ne_store {p : Primitive} (h : Interactive p) : p ≠ .store := by
  rcases h with rfl | rfl | ⟨o,rfl⟩ <;> intro eq <;> cases eq

/-- Lift one interaction when its entire ordered edge frame survives in a common occurrence space. -/
theorem lift_step {d r I O J K} {W : Type} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : G.Vertex → W) (g : H.Vertex → W) (inj : Function.Injective g)
    {p q : Position G} {u : Position H} (step : Step G p q)
    (token : mapPosition g u = mapPosition f p)
    (edges : ∀ e primitive, G.edgeLabel e = primitiveLabel d primitive → Interactive primitive → Uses G p e →
      ∃ b, H.edgeLabel b = primitiveLabel r primitive ∧
        (H.source b).map g = (G.source e).map f ∧ (H.target b).map g = (G.target e).map f) :
    ∃ t, Step H u t ∧ mapPosition g t = mapPosition f q := by
  obtain ⟨mode,port⟩ := Prod.mk.inj token
  cases step with
  | search e primitive v q label src result =>
    obtain ⟨b,bl,bs,bt⟩ := edges e primitive label (enter_interactive result) (.inl ⟨rfl,src⟩)
    have member : u.2 ∈ H.source b := by
      have m : g u.2 ∈ (H.source b).map g := by rw [bs,port]; exact List.mem_map_of_mem src
      obtain ⟨x,hx,eq⟩ := List.mem_map.mp m
      exact inj eq ▸ hx
    have outcome : Option.map (mapPosition g) (enter primitive u.2 (H.target b)) = some (mapPosition f q) := by
      unfold mapPosition
      rw [← enter_map,bt,port,enter_map,result]; rfl
    obtain ⟨t,ht,eq⟩ := Option.map_eq_some_iff.mp outcome
    refine ⟨t,?_,eq⟩
    have st := Step.search (G := H) b primitive u.2 t bl member ht
    have same : u = (.search,u.2) := Prod.ext mode rfl
    exact same ▸ st
  | backtrack e o root v j q label src bound arg result =>
    obtain ⟨b,bl,bs,bt⟩ := edges e (.operation o) label (.inr (.inr ⟨o,rfl⟩)) (.inr ⟨rfl,j,arg⟩)
    have one : (H.source b).length = 1 := by
      have h := congrArg List.length bs
      simpa [src] using h
    obtain ⟨a,source⟩ := List.length_eq_one_iff.mp one
    have parent : g a = f root := by rw [source,src] at bs; exact (List.cons.inj bs).1
    have argument : (H.target b)[j]? = some u.2 := by
      apply (Option.map_injective inj)
      rw [← List.getElem?_map,bt,List.getElem?_map,arg]
      exact congrArg some port.symm
    have outcome : Option.map (mapPosition g) (resume o a (H.target b) j) = some (mapPosition f q) := by
      unfold mapPosition
      rw [← resume_map,bt,parent,resume_map,result]; rfl
    obtain ⟨t,ht,eq⟩ := Option.map_eq_some_iff.mp outcome
    refine ⟨t,?_,eq⟩
    have st := Step.backtrack (G := H) b o a u.2 j t bl source bound argument ht
    have same : u = (.backtrack,u.2) := Prod.ext mode rfl
    exact same ▸ st

/-- Replay a pre-head prefix when all actually used frames survive; histories certify avoidance. -/
theorem lift_prefix {d r I O J K} {W : Type} {G : Hypernet d I O} {H : Hypernet r J K}
    (f : G.Vertex → W) (g : H.Vertex → W) (inj : Function.Injective g) {i v}
    (edges : ∀ n p, History G i n p → ¬ Visit G i n p v →
      ∀ e primitive, G.edgeLabel e = primitiveLabel d primitive → Interactive primitive → Uses G p e →
      ∃ b, H.edgeLabel b = primitiveLabel r primitive ∧
        (H.source b).map g = (G.source e).map f ∧ (H.target b).map g = (G.target e).map f)
    {n k s u z a} (initialRun : (machine G).Steps n (.search,.input i) s)
    (rest : (machine G).Steps k s (.search,v)) (finish : (machine G).Steps a (.search,v) z)
    (mode : z.1 = .rewrite) (token : mapPosition g u = mapPosition f s) :
    ∃ t, (machine H).Steps k u t ∧ mapPosition g t = mapPosition f (.search,v) := by
  induction k generalizing n s u with
  | zero => cases rest; exact ⟨u,.zero _,token⟩
  | succ k ih =>
    have avoid : ¬ Visit G i n s v := fun visit => visit.no_earlier_cycle rest (by omega) finish mode
    cases rest with
    | cons step tail =>
      obtain ⟨t,st,eq⟩ := lift_step f g inj step token (edges n s (history initialRun) avoid)
      obtain ⟨q,run,endpoint⟩ := ih (initialRun.append (.cons step (.zero _))) tail eq
      exact ⟨q,.cons st run,endpoint⟩

/-- A surviving prefix and token equation prove rootedness, without assuming it on the reduct. -/
theorem rooted_of_frames {d r I O} {W : Type} {G : Hypernet d I O} {H : Hypernet r I O}
    (f : G.Vertex → W) (g : H.Vertex → W) (inj : Function.Injective g) {i v w}
    (input : g (.input i) = f (.input i)) (token : g w = f v)
    (edges : ∀ n p, History G i n p → ¬ Visit G i n p v →
      ∀ e primitive, G.edgeLabel e = primitiveLabel d primitive → Interactive primitive → Uses G p e →
      ∃ b, H.edgeLabel b = primitiveLabel r primitive ∧
        (H.source b).map g = (G.source e).map f ∧ (H.target b).map g = (G.target e).map f)
    (root : RootedFrom G i (.rewrite,v)) : RootedFrom H i (.search,w) := by
  obtain ⟨n,run⟩ := root
  obtain ⟨a,b,_,_,initialRun,finish⟩ := revisit run (by intro h; cases h)
  obtain ⟨t,run,eq⟩ := lift_prefix (G := G) (H := H) f g inj edges (n := 0) (u := (.search,.input i)) (.zero _) initialRun finish rfl (Prod.ext rfl input)
  change (t.1,g t.2) = (.search,f v) at eq
  have same : t = (.search,w) := Prod.ext (Prod.mk.inj eq).1 (inj ((Prod.mk.inj eq).2.trans token.symm))
  exact ⟨a,same ▸ run⟩
end Hypernets.Copying.Search

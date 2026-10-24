import Hypernets.Graph.DepthPadding

/-! Exact recursive occurrence inventories under depth padding. -/
namespace Hypernets.Linear.DepthPadding
open Graph
variable {Op : Type} {ops : Operations Op}

/-- Inventory isomorphisms may compare different depth allowances. -/
structure InventoryIso {n m I O} (G : Hypernet ops n I O) (H : Hypernet ops m I O) where
  occurrences : Bijection (AllEdge ops n G) (AllEdge ops m H)
  hole : ∀ a, holeAt ops m H (occurrences.toFun a) = holeAt ops n G a

/-- The label-local version includes shallow and nested occurrences. -/
structure FiberIso {n m} (p : (alphabet ops n).Symbol) (q : (alphabet ops m).Symbol) where
  occurrences : Bijection (Fiber ops n p) (Fiber ops m q)
  hole : ∀ a, fiberHole ops m q (occurrences.toFun a) = fiberHole ops n p a

/-- Assemble local fibre bijections without changing the surrounding edge carrier. -/
def assemble {n I O} (G : Hypernet ops n I O)
    (fibers : ∀ e, FiberIso (G.edgeLabel e) (label n (G.edgeLabel e))) : InventoryIso G (graph G) := by
  let occurrence : Bijection (Occurrences G) (Occurrences (graph G)) := {
    toFun a := ⟨a.1,(fibers a.1).occurrences.toFun a.2⟩
    invFun a := ⟨a.1,(fibers a.1).occurrences.invFun a.2⟩
    left_inv a := by rcases a with ⟨e,a⟩; simp only [(fibers e).occurrences.left_inv]
    right_inv a := by rcases a with ⟨e,a⟩; exact congrArg (Sigma.mk e) ((fibers e).occurrences.right_inv a) }
  refine ⟨((occurrenceBijection ops n G).trans occurrence).trans
    (occurrenceBijection ops (n+1) (graph G)).symm,?_⟩
  intro a
  change holeAt ops (n+1) (graph G) ((occurrenceBijection ops (n+1) (graph G)).invFun
    (occurrence.toFun ((occurrenceBijection ops n G).toFun a))) = _
  rw [← occurrenceBijection_hole, (occurrenceBijection ops (n+1) (graph G)).right_inv]
  exact ((fibers _).hole _).trans (occurrenceBijection_hole n G a)

/-- Padding gives an exact bijection of all shallow and nested hole addresses. -/
def inventory (n : Nat) {I O} (G : Hypernet ops n I O) : InventoryIso G (graph G) := by
  induction n generalizing I O with
  | zero =>
    apply assemble G
    intro e
    exact ⟨Bijection.refl _,by rintro (u | x); rfl; exact nomatch x⟩
  | succ n ih =>
    apply assemble G
    intro e
    generalize G.edgeLabel e = p
    cases p with
    | inl p => exact ⟨Bijection.refl _,by rintro (u | x); rfl; exact nomatch x⟩
    | inr b =>
      have body : InventoryIso b.body (raise ops n b.body) := by
        rw [← graph_eq_raise]
        exact ih b.body
      refine ⟨(Bijection.refl Unit).sum body.occurrences,?_⟩
      rintro (u | x)
      · rfl
      · exact body.hole x

namespace InventoryIso
variable {n m I O} {G : Hypernet ops n I O} {H : Hypernet ops m I O} (f : InventoryIso G H)

include f

theorem hasHole_iff (h : Hole) : HasHole H h ↔ HasHole G h := by
  constructor
  · rintro ⟨a,ha⟩
    exact ⟨f.occurrences.invFun a,(f.hole _).symm.trans (by simpa only [f.occurrences.right_inv] using ha)⟩
  · rintro ⟨a,ha⟩
    exact ⟨f.occurrences.toFun a,(f.hole a).trans ha⟩

theorem holeFree_iff : HoleFree H ↔ HoleFree G :=
  ⟨fun h x hx => h x ((f.hasHole_iff x).mpr hx),fun h x hx => h x ((f.hasHole_iff x).mp hx)⟩

theorem unique_iff : UniqueHoles ops m H ↔ UniqueHoles ops n G := by
  constructor
  · intro unique h a b ha hb
    apply f.occurrences.injective
    exact unique h _ _ ((f.hole a).trans ha) ((f.hole b).trans hb)
  · intro unique h a b ha hb
    have same := unique h (f.occurrences.invFun a) (f.occurrences.invFun b)
      ((f.hole _).symm.trans (by simpa only [f.occurrences.right_inv] using ha))
      ((f.hole _).symm.trans (by simpa only [f.occurrences.right_inv] using hb))
    simpa only [f.occurrences.right_inv] using congrArg f.occurrences.toFun same
end InventoryIso

/-- Actual closed focussed states can be padded without adding an execution step. -/
def state {n : Nat} (s : State ops n) : State ops (n+1) where
  graph := graph s.graph
  focussed := focussed s.focussed
  hole_free := (inventory n s.graph).holeFree_iff.mpr s.hole_free

theorem state_initial_iff {n : Nat} (s : State ops n) :
    (state s).focussed.Initial ↔ s.focussed.Initial := Iff.rfl

theorem state_final_iff {n : Nat} (s : State ops n) :
    (state s).focussed.Final ↔ s.focussed.Final := Iff.rfl
end Hypernets.Linear.DepthPadding

import Hypernets.Copying.Translation

/-! The annotated lambda-context grammar of Section 11. A hole carries its
own variable and atom scope, including variables bound by enclosing lambdas. -/
namespace Hypernets.Copying

inductive TermContext (variables atoms : Nat) : Nat → Nat → Type where
  | hole : TermContext variables atoms variables atoms
  | lam {k h} : TermContext variables atoms (k+1) h → TermContext variables atoms k h
  | appLeft {k h} : TermContext variables atoms k h → Term k h → TermContext variables atoms k h
  | appRight {k h} : Term k h → TermContext variables atoms k h → TermContext variables atoms k h
  | unary {k h} : Unary → TermContext variables atoms k h → TermContext variables atoms k h
  | binaryLeft {k h} : Binary → TermContext variables atoms k h → Term k h → TermContext variables atoms k h
  | binaryRight {k h} : Binary → Term k h → TermContext variables atoms k h → TermContext variables atoms k h

namespace TermContext

def fill {v a k h} (C : TermContext v a k h) (t : Term v a) : Term k h :=
  match C with
  | .hole => t
  | .lam C => .lam (C.fill t)
  | .appLeft C u => .app (C.fill t) u
  | .appRight u C => .app u (C.fill t)
  | .unary o C => .unary o (C.fill t)
  | .binaryLeft o C u => .binary o (C.fill t) u
  | .binaryRight o u C => .binary o u (C.fill t)

/-- Substitute one annotated context into another, without changing scopes. -/
def compose {v a k h l j} (C : TermContext k h l j) (D : TermContext v a k h) :
    TermContext v a l j :=
  match C with
  | .hole => D
  | .lam C => .lam (C.compose D)
  | .appLeft C u => .appLeft (C.compose D) u
  | .appRight u C => .appRight u (C.compose D)
  | .unary o C => .unary o (C.compose D)
  | .binaryLeft o C u => .binaryLeft o (C.compose D) u
  | .binaryRight o u C => .binaryRight o u (C.compose D)

theorem fill_compose {v a k h l j} (C : TermContext k h l j)
    (D : TermContext v a k h) (t : Term v a) :
    (C.compose D).fill t = C.fill (D.fill t) := by
  induction C <;> simp_all [compose,fill]

theorem compose_hole {v a k h} (C : TermContext v a k h) : C.compose .hole = C := by
  induction C <;> simp_all [compose]

theorem compose_assoc {v a k h l j m p} (C : TermContext l j m p)
    (D : TermContext k h l j) (E : TermContext v a k h) :
    (C.compose D).compose E = C.compose (D.compose E) := by
  induction C <;> simp_all [compose]
end TermContext

namespace ContextTranslation
open Graph

/-- Package the exact finite depth with its graph, without quotienting or
changing the graph. This avoids arbitrary common-depth choices in contexts. -/
abbrev ScopedGraph (k h : Nat) := (d : Nat) × Hypernet d [.term] (environmentInterface k h)

def ofTerm {k h} (t : Term k h) : ScopedGraph k h := ⟨Translation.depth t,Translation.term t⟩

def abstraction {k h} (G : ScopedGraph (k+1) h) : ScopedGraph k h :=
  ⟨G.1+1,Translation.abstraction G.2⟩

def unary {k h} (o : Unary) (G : ScopedGraph k h) : ScopedGraph k h :=
  ⟨G.1,Translation.unary o G.2⟩

def application {k h} (G H : ScopedGraph k h) : ScopedGraph k h :=
  ⟨max G.1 H.1,Translation.application
    (Translation.padTo _ (Nat.le_max_left _ _) G.2)
    (Translation.padTo _ (Nat.le_max_right _ _) H.2)⟩

def binary {k h} (o : Binary) (G H : ScopedGraph k h) : ScopedGraph k h :=
  ⟨max G.1 H.1,Translation.binary o
    (Translation.padTo _ (Nat.le_max_left _ _) G.2)
    (Translation.padTo _ (Nat.le_max_right _ _) H.2)⟩

/-- Figure 16's constructors extended parametrically to an annotated hole.
Supplying a hole corolla below gives the actual holed graph. -/
def apply {v a k h} (C : TermContext v a k h) (G : ScopedGraph v a) : ScopedGraph k h :=
  match C with
  | .hole => G
  | .lam C => abstraction (apply C G)
  | .appLeft C u => application (apply C G) (ofTerm u)
  | .appRight u C => application (ofTerm u) (apply C G)
  | .unary o C => unary o (apply C G)
  | .binaryLeft o C u => binary o (apply C G) (ofTerm u)
  | .binaryRight o u C => binary o (ofTerm u) (apply C G)

/-- The extension reconstructs the unchanged original term translation,
including its exact depth, when supplied with the translated hole content. -/
theorem apply_ofTerm {v a k h} (C : TermContext v a k h) (t : Term v a) :
    apply C (ofTerm t) = ofTerm (C.fill t) := by
  induction C with
  | hole => rfl
  | lam C ih => change abstraction (apply C (ofTerm t)) = _; rw [ih]; rfl
  | appLeft C u ih => change application (apply C (ofTerm t)) (ofTerm u) = _; rw [ih]; rfl
  | appRight u C ih => change application (ofTerm u) (apply C (ofTerm t)) = _; rw [ih]; rfl
  | unary o C ih => change unary o (apply C (ofTerm t)) = _; rw [ih]; rfl
  | binaryLeft o C u ih => change binary o (apply C (ofTerm t)) (ofTerm u) = _; rw [ih]; rfl
  | binaryRight o u C ih => change binary o (ofTerm u) (apply C (ofTerm t)) = _; rw [ih]; rfl

/-- Composition of constructor contexts is literal composition of their graph
interpretations. This is not yet the addressed graph-plugging theorem. -/
theorem apply_compose {v a k h l j} (C : TermContext k h l j)
    (D : TermContext v a k h) (G : ScopedGraph v a) :
    apply (C.compose D) G = apply C (apply D G) := by
  induction C <;> simp_all [apply,TermContext.compose]

/-- Translate the annotated hole to the paper's single hole edge, at any
chosen allowance. All surrounding term constructors remain unchanged. -/
def hole (d name k h : Nat) : ScopedGraph k h :=
  ⟨d,primitiveNet d (.hole ⟨name,[.term],environmentInterface k h⟩)⟩

def graph {v a k h} (C : TermContext v a k h) (d name : Nat) : ScopedGraph k h :=
  apply C (hole d name v a)

theorem graph_compose {v a k h l j} (C : TermContext k h l j)
    (D : TermContext v a k h) (d name : Nat) :
    graph (C.compose D) d name = apply C (graph D d name) := apply_compose C D _
end ContextTranslation
end Hypernets.Copying

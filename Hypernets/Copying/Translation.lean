import Hypernets.Copying.BinaryTranslation

/-! The full Figure 16 translation, with the original scoped term datatype.
Padding changes only the finite representation allowance, not graph structure. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Translation
open Graph

/-- Change a provably equal depth index; neither terms nor graph incidence change. -/
def castDepth {d n I O} (eq : d = n) (G : Hypernet d I O) : Hypernet n I O := eq ▸ G

theorem allLabels_castDepth (P : Primitive → Prop) {d n I O} (eq : d = n) (G : Hypernet d I O) :
    AllLabels P (castDepth eq G) ↔ AllLabels P G := by cases eq; rfl

/-- Add unused depth allowance by the previously defined recursive padding. -/
def pad (d : Nat) {I O} : (n : Nat) → Hypernet d I O → Hypernet (d+n) I O
  | 0, G => G
  | n+1, G => raise (d+n) (pad d n G)

theorem allLabels_pad (P : Primitive → Prop) (d n : Nat) {I O} (G : Hypernet d I O) :
    AllLabels P (pad d n G) ↔ AllLabels P G := by
  induction n with
  | zero => rfl
  | succ n ih => exact (allLabels_raise_iff P _ _).trans ih

/-- Raise a graph to a common allowance chosen by the caller. -/
def padTo {d I O} (n : Nat) (bound : d ≤ n) (G : Hypernet d I O) : Hypernet n I O :=
  castDepth (Nat.add_sub_of_le bound) (pad d (n-d) G)

theorem allLabels_padTo (P : Primitive → Prop) {d I O} (n : Nat) (bound : d ≤ n) (G : Hypernet d I O) :
    AllLabels P (padTo n bound G) ↔ AllLabels P G :=
  (allLabels_castDepth _ _ _).trans (allLabels_pad _ _ _ _)

/-- Increasing depth allowance does not allocate any additional outer edge. -/
theorem raise_edgeCount (d : Nat) {I O} (G : Hypernet d I O) :
    (raise d G).finiteEdge.elements.length = G.finiteEdge.elements.length := by
  cases d <;> rfl

theorem pad_edgeCount (d n : Nat) {I O} (G : Hypernet d I O) :
    (pad d n G).finiteEdge.elements.length = G.finiteEdge.elements.length := by
  induction n with
  | zero => rfl
  | succ n ih => exact (raise_edgeCount _ _).trans ih

theorem castDepth_edgeCount {d n I O} (eq : d = n) (G : Hypernet d I O) :
    (castDepth eq G).finiteEdge.elements.length = G.finiteEdge.elements.length := by
  cases eq; rfl

theorem padTo_edgeCount {d I O} (n : Nat) (bound : d ≤ n) (G : Hypernet d I O) :
    (padTo n bound G).finiteEdge.elements.length = G.finiteEdge.elements.length :=
  (castDepth_edgeCount _ _).trans (pad_edgeCount _ _ _)

/-- Only abstraction increases the needed box allowance. -/
def depth {k h} : Term k h → Nat
  | .var _ | .atom _ | .const _ => 0
  | .lam t => depth t + 1
  | .app t u | .binary _ t u => max (depth t) (depth u)
  | .unary _ t => depth t

/-- Environment renaming, including weakening, does not change the box allowance. -/
theorem depth_rename {k h} (t : Term k h) {l j} (ρ : Fin k → Fin l) (α : Fin h → Fin j) :
    depth (Term.rename ρ α t) = depth t := by
  induction t generalizing l j with
  | lam t ih => simp [Term.rename, depth, ih]
  | _ => simp_all [Term.rename, depth]

/-- Figure 16, recursively assembled without changing its terms or sharing graphs. -/
def term {k h} : (t : Term k h) → Hypernet (depth t) [.term] (environmentInterface k h)
  | .var i => variableTerm 0 h i
  | .atom a => atom 0 k a
  | .const c => constant 0 k h c
  | .lam t => abstraction (term t)
  | .app t u => application
      (padTo _ (Nat.le_max_left _ _) (term t))
      (padTo _ (Nat.le_max_right _ _) (term u))
  | .unary o t => unary o (term t)
  | .binary o t u => binary o
      (padTo _ (Nat.le_max_left _ _) (term t))
      (padTo _ (Nat.le_max_right _ _) (term u))

/-- Every translated term belongs to the full example language, at every box depth. -/
theorem term_language {k h} (t : Term k h) : LanguageGraph (term t) := by
  induction t with
  | var i => exact variable_language _ _ _
  | atom a => exact atom_language _ _ _
  | const c => exact constant_language _ _ _ _
  | lam t ih => exact abstraction_language ih
  | unary o t ih => exact unary_language o ih
  | app t u ih jh =>
    exact application_language ((allLabels_padTo _ _ _ _).mpr ih) ((allLabels_padTo _ _ _ _).mpr jh)
  | binary o t u ih jh =>
    exact binary_language o ((allLabels_padTo _ _ _ _).mpr ih) ((allLabels_padTo _ _ _ _).mpr jh)

theorem term_focusFree {k h} (t : Term k h) : FocusFree (term t) := language_focusFree (term_language t)

theorem term_holeFree {k h} (t : Term k h) : HoleFree (term t) := language_holeFree (term_language t)

/-- Named distinct-list environments are exposed without restricting their sizes. -/
def inEnvironment {Name : Type} (E : Environment Name) (t : Term E.variables.length E.atoms.length) :
    Hypernet (depth t) [.term] (environmentInterface E.variables.length E.atoms.length) := term t

/-- The actual left-hand program of Proposition 12.2, unchanged. -/
def privateCell (k h : Nat) := term (Term.privateCell k h)

/-- The actual right-hand program of Proposition 12.2, unchanged. -/
def constantResult (k h : Nat) := term (Term.constantResult k h)

theorem privateCell_language (k h : Nat) : LanguageGraph (privateCell k h) := term_language _

theorem constantResult_language (k h : Nat) : LanguageGraph (constantResult k h) := term_language _

end Hypernets.Copying.Translation

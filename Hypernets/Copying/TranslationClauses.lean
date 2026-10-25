import Hypernets.Copying.Distributor
import Hypernets.Copying.Serial
import Hypernets.Graph.Tensor

/-! Literal graph-building clauses of Figure 16. Single-use distributors remain
present. These constructors do not redefine or simplify the proposition's terms. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace Translation

/-- Change only provably equal interface indices, without modifying the graph. -/
def castInterfaces {d I O J K} (hi : I = J) (ho : O = K) (G : Hypernet d I O) : Hypernet d J K :=
  hi ▸ ho ▸ G

theorem allLabels_cast (P : Primitive → Prop) {d I O J K} (hi : I = J) (ho : O = K)
    (G : Hypernet d I O) : AllLabels P (castInterfaces hi ho G) ↔ AllLabels P G := by
  cases hi; cases ho; rfl

/-- Juxtaposition of term and atom distributors, with variables before atoms. -/
def environmentDistributor (d k h m : Nat) :
    Hypernet d (environmentInterface (k*m) (h*m)) (environmentInterface k h) :=
  Net.Tensor.net (Distributor.atDepth .term k m d) (Distributor.atDepth .atom h m d)

/-- The paper adds these distributors even for a single subterm. -/
def singleUse (d k h : Nat) : Hypernet d (environmentInterface k h) (environmentInterface k h) :=
  castInterfaces (by simp) rfl (environmentDistributor d k h 1)

/-- Figure 16's selected resource: D_{i,0}, D_{1,1}, D_{n-i-1,0} in that order. -/
def selectedResource (d : Nat) (s : ShareSort) {n : Nat} (i : Fin n) :
    Hypernet d [s.wire] (List.replicate n s.wire) :=
  castInterfaces (by simp)
    (by
      change (List.replicate i.val s.wire ++ List.replicate 1 s.wire) ++
        List.replicate (n-i.val-1) s.wire = List.replicate n s.wire
      rw [List.replicate_append_replicate, List.replicate_append_replicate]
      congr 1
      have := i.isLt
      omega)
    (Net.Tensor.net (Net.Tensor.net (Distributor.atDepth s i.val 0 d)
      (Distributor.atDepth s 1 1 d)) (Distributor.atDepth s (n-i.val-1) 0 d))

/-- Figure 16's variable clause, with weakening of all unused variables and atoms. -/
def variableTerm (d : Nat) {k : Nat} (h : Nat) (i : Fin k) :
    Hypernet d [.term] (environmentInterface k h) :=
  castInterfaces (by simp [ShareSort.wire]) rfl
    (Net.Tensor.net (selectedResource d .term i) (Distributor.atDepth .atom h 0 d))

/-- Figure 16's atom clause retains the instance edge and the atom D_{1,1}. -/
def atom (d : Nat) (k : Nat) {h : Nat} (a : Fin h) :
    Hypernet d [.term] (environmentInterface k h) :=
  castInterfaces (by simp [primitiveSignature]) rfl
    (Net.Tensor.net (Distributor.atDepth .term k 0 d)
      (Serial.net (primitiveNet d .instanceEdge) (selectedResource d .atom a)))

/-- Figure 16's constant clause retains weakening for every ambient variable and atom. -/
def constant (d k h : Nat) (c : Constant) : Hypernet d [.term] (environmentInterface k h) :=
  castInterfaces (by simp [primitiveSignature]) (by simp [environmentInterface, primitiveSignature, Operation.outputs, ShareSort.wire])
    (Net.Tensor.net (Net.Tensor.net (Distributor.atDepth .term k 0 d)
      (primitiveNet d (.operation (.const c)))) (Distributor.atDepth .atom h 0 d))

/-- Figure 16's unary clause: operation, translated subterm, then both distributors. -/
def unary {d k h} (o : Unary) (G : Hypernet d [.term] (environmentInterface k h)) :
    Hypernet d [.term] (environmentInterface k h) :=
  Serial.net (Serial.net (primitiveNet d (.operation (.unary o))) G) (singleUse d k h)

/-- The lambda body's first variable is bound; the others remain free and ordered. -/
def lambdaBox {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.thunk 1] (environmentInterface k h) :=
  box (bound := 1) (freeVariables := k) (freeAtoms := h) (castInterfaces rfl (by rw [Nat.add_comm k 1]) G)

/-- Figure 16's abstraction clause, retaining the outer single-use distributors. -/
def abstraction {d k h} (G : Hypernet d [.term] (environmentInterface (k+1) h)) :
    Hypernet (d+1) [.term] (environmentInterface k h) :=
  Serial.net (Serial.net (primitiveNet (d+1) (.operation .lam)) (lambdaBox G)) (singleUse (d+1) k h)

/-- The term-translation alphabet excludes store, focus, and hole primitives. -/
def LanguagePrimitive : Primitive → Prop
  | .operation _ | .contraction _ | .weakening _ | .instanceEdge => True
  | .store | .focus _ | .hole _ => False

def LanguageGraph {d I O} (G : Hypernet d I O) : Prop := AllLabels LanguagePrimitive G

theorem allLabels_tensor (P : Primitive → Prop) {d I O J K}
    {G : Hypernet d I O} {H : Hypernet d J K} (g : AllLabels P G) (h : AllLabels P H) :
    AllLabels P (Net.Tensor.net G H) :=
  (Net.Tensor.labels_iff G H (LabelAll P d)).mpr ⟨g,h⟩

theorem allLabels_primitive (P : Primitive → Prop) (d : Nat) (p : Primitive) (h : P p) :
    AllLabels P (primitiveNet d p) := by
  intro e
  cases d <;> exact h

theorem environmentDistributor_language (d k h m : Nat) : LanguageGraph (environmentDistributor d k h m) :=
  allLabels_tensor _ (Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial)
    (Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial)

theorem singleUse_language (d k h : Nat) : LanguageGraph (singleUse d k h) := by
  exact (allLabels_cast _ _ _ _).mpr (environmentDistributor_language d k h 1)

theorem selectedResource_language (d : Nat) (s : ShareSort) {n : Nat} (i : Fin n) :
    LanguageGraph (selectedResource d s i) := by
  apply (allLabels_cast _ _ _ _).mpr
  apply allLabels_tensor
  · apply allLabels_tensor
    all_goals exact Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial
  · exact Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial

theorem variable_language (d : Nat) {k : Nat} (h : Nat) (i : Fin k) : LanguageGraph (variableTerm d h i) :=
  (allLabels_cast _ _ _ _).mpr (allLabels_tensor _ (selectedResource_language _ _ _)
    (Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial))

theorem atom_language (d : Nat) (k : Nat) {h : Nat} (a : Fin h) : LanguageGraph (atom d k a) :=
  (allLabels_cast _ _ _ _).mpr (allLabels_tensor _
    (Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial)
    (Serial.allLabels_net _ (allLabels_primitive _ _ _ trivial) (selectedResource_language _ _ _)))

theorem constant_language (d k h : Nat) (c : Constant) : LanguageGraph (constant d k h c) := by
  apply (allLabels_cast _ _ _ _).mpr
  apply allLabels_tensor
  · apply allLabels_tensor
    · exact Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial
    · exact allLabels_primitive _ _ _ trivial
  · exact Distributor.allLabels_atDepth _ _ _ _ _ trivial trivial

theorem unary_language {d k h} (o : Unary) {G : Hypernet d [.term] (environmentInterface k h)}
    (g : LanguageGraph G) : LanguageGraph (unary o G) :=
  Serial.allLabels_net _ (Serial.allLabels_net _ (allLabels_primitive _ _ _ trivial) g)
    (singleUse_language d k h)

theorem lambdaBox_language {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    (g : LanguageGraph G) : LanguageGraph (lambdaBox G) := by
  intro e
  exact (allLabels_cast _ _ _ _).mpr g

theorem abstraction_language {d k h} {G : Hypernet d [.term] (environmentInterface (k+1) h)}
    (g : LanguageGraph G) : LanguageGraph (abstraction G) :=
  Serial.allLabels_net _ (Serial.allLabels_net _ (allLabels_primitive _ _ _ trivial) (lambdaBox_language g))
    (singleUse_language (d+1) k h)

/-- The constructed language fragment is globally focus-free, including box bodies. -/
theorem language_focusFree {d I O} {G : Hypernet d I O} (g : LanguageGraph G) : FocusFree G := by
  -- Lift implication through arbitrary nested boxes.
  have mono : ∀ d (p : (alphabet d).Symbol), LabelAll LanguagePrimitive d p →
      LabelAll (fun p => ∀ m, p ≠ .focus m) d p := by
    intro d
    induction d with
    | zero => intro p h m eq; cases p; cases eq; exact h
    | succ d ih =>
      intro p h
      cases p with
      | inl p => intro m eq; cases eq; exact h
      | inr b => intro e; exact ih _ (h e)
  intro e
  exact mono d _ (g e)

theorem language_holeFree {d I O} {G : Hypernet d I O} (g : LanguageGraph G) : HoleFree G := by
  have mono : ∀ d (p : (alphabet d).Symbol), LabelAll LanguagePrimitive d p →
      LabelAll (fun p => ∀ h, p ≠ .hole h) d p := by
    intro d
    induction d with
    | zero => intro p h hole eq; cases p; cases eq; exact h
    | succ d ih =>
      intro p h
      cases p with
      | inl p => intro hole eq; cases eq; exact h
      | inr b => intro e; exact ih _ (h e)
  intro e
  exact mono d _ (g e)

end Translation
end Hypernets.Copying

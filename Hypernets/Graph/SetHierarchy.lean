import Hypernets.Graph.SetPresentation
import Hypernets.Graph.RecursiveIso

/-! Set-based presentation of the finite linear box hierarchy. -/
namespace Hypernets.Linear.SetHierarchy
open Graph
variable {Op : Type} (ops : Operations Op)

/-- A box with an arbitrary-vertex set graph for its content. -/
structure SetBox (A : Alphabet) where
  bound : Nat
  free : Nat
  body : SetNet A.signature [.term] (List.replicate (bound + free) .term)

/-- Add graph-labelled boxes to a set-graph alphabet. -/
def nextAlphabet (A : Alphabet) : Alphabet where
  Symbol := Primitive Op ⊕ SetBox A
  signature := {
    input | .inl p => (primitiveSignature ops).input p | .inr b => [.thunk b.bound]
    output | .inl p => (primitiveSignature ops).output p | .inr b => List.replicate b.free .term
  }

/-- An annotated graph-labelled hierarchy, with ordinary vertex sets at every level. -/
@[reducible] def alphabet : Nat → Alphabet
  | 0 => baseAlphabet ops
  | n+1 => nextAlphabet ops (alphabet n)

abbrev Hypernet (n : Nat) (I O : List Wire) := SetNet (alphabet ops n).signature I O

/-- Normalize every box body as well as the outer vertex set. -/
noncomputable def normalize : (n : Nat) → {I O : List Wire} → Hypernet ops n I O → Linear.Hypernet ops n I O
  | 0,_,_,G => G.toNet
  | n+1,_,_,G => G.toNet.relabel _
      (fun p => match p with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.free,normalize n b.body⟩)
      (by intro p; cases p <;> rfl) (by intro p; cases p <;> rfl)

/-- Expose arbitrary vertex sets recursively, including inside box labels. -/
noncomputable def expose : (n : Nat) → {I O : List Wire} → Linear.Hypernet ops n I O → Hypernet ops n I O
  | 0,_,_,G => G.toSet
  | n+1,_,_,G => G.toSet.relabel _
      (fun p => match p with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.free,expose n b.body⟩)
      (by intro p; cases p <;> rfl) (by intro p; cases p <;> rfl)

/-- Exposure followed by normalization retains the entire typed hierarchy. -/
noncomputable def typed_roundtrip : (n : Nat) → {I O : List Wire} → (G : Linear.Hypernet ops n I O) →
    DeepIso G (normalize ops n (expose ops n G))
  | 0,_,_,G => DeepIso.ofIso (Net.roundtrip G)
  | n+1,_,_,G => {
      vertices := G.interiorBijection
      edges := Bijection.refl _
      internal_label := fun _ => rfl
      edge_label := by
        intro e
        cases eq : G.edgeLabel e with
        | inl p => simp [normalize,expose,Net.toSet,SetNet.toNet,Net.relabel,SetNet.relabel,Bijection.refl,id_eq,eq,Linear.LabelEquiv]
        | inr b =>
          simp only [normalize,expose,Net.toSet,SetNet.toNet,Net.relabel,SetNet.relabel,Bijection.refl,id_eq,eq]
          exact .bodies ⟨typed_roundtrip n b.body⟩
      source := (Net.roundtrip G).source
      target := (Net.roundtrip G).target
    }

/-- Recursive comparison of set-box labels includes the ordered binder split. -/
inductive BoxRelated (A : Alphabet)
    (R : ∀ {I O}, SetNet A.signature I O → SetNet A.signature I O → Prop) : SetBox A → SetBox A → Prop where
  | bodies {bound free} {G H : SetNet A.signature [.term] (List.replicate (bound+free) .term)}
      (related : R G H) : BoxRelated A R ⟨bound,free,G⟩ ⟨bound,free,H⟩

/-- Equality of primitives and recursive boundary-preserving isomorphism of contents. -/
def LabelEquiv : (n : Nat) → (alphabet ops n).Symbol → (alphabet ops n).Symbol → Prop
  | 0,a,b => a = b
  | _+1,.inl a,.inl b => a = b
  | n+1,.inr a,.inr b => BoxRelated (alphabet ops n)
      (fun G H => Nonempty (SetNet.RelIso (LabelEquiv n) G H)) a b
  | _+1,_,_ => False

abbrev DeepIso {n I O} (G H : Hypernet ops n I O) := SetNet.RelIso (LabelEquiv ops n) G H

/-- Normalization followed by exposure retains the original arbitrary vertex names
up to a bijection, independently at every nesting level. -/
noncomputable def set_roundtrip : (n : Nat) → {I O : List Wire} → (G : Hypernet ops n I O) →
    DeepIso ops G (expose ops n (normalize ops n G))
  | 0,_,_,G => {
      vertices := G.vertices
      edges := Bijection.refl _
      vertex_label := G.encode_label
      edge_label := fun _ => rfl
      input := fun i => G.encode_decode (.input i)
      output := fun j => G.encode_decode (.output j)
      source := fun _ => rfl
      target := fun _ => rfl
    }
  | n+1,_,_,G => {
      vertices := G.vertices
      edges := Bijection.refl _
      vertex_label := G.encode_label
      edge_label := by
        intro e
        cases eq : G.edgeLabel e with
        | inl p => simp [normalize,expose,Net.toSet,SetNet.toNet,Net.relabel,SetNet.relabel,Bijection.refl,id_eq,eq,LabelEquiv]
        | inr b =>
          simp only [normalize,expose,Net.toSet,SetNet.toNet,Net.relabel,SetNet.relabel,Bijection.refl,id_eq,eq]
          exact .bodies ⟨set_roundtrip n b.body⟩
      input := fun i => G.encode_decode (.input i)
      output := fun j => G.encode_decode (.output j)
      source := fun _ => rfl
      target := fun _ => rfl
    }

/-- The metadata is determined by the external type: it is not an additional
choice once the typed box incidence is fixed. -/
theorem metadata_unique {A : Alphabet} (b c : SetBox A)
    (input : ([Wire.thunk b.bound] : List Wire) = [.thunk c.bound])
    (output : List.replicate b.free Wire.term = List.replicate c.free Wire.term) :
    b.bound = c.bound ∧ b.free = c.free := by
  exact ⟨Wire.thunk.inj (List.cons.inj input).1,by simpa using congrArg List.length output⟩

/-- Enlarge a set hierarchy's depth allowance without changing its graph. -/
noncomputable def raise : (n : Nat) → {I O : List Wire} → Hypernet ops n I O → Hypernet ops (n+1) I O
  | 0,_,_,G => G.relabel _ (fun p => .inl p.down) (fun _ => rfl) (fun _ => rfl)
  | n+1,_,_,G => G.relabel _
      (fun p => match p with
        | .inl p => .inl p
        | .inr b => .inr ⟨b.bound,b.free,raise n b.body⟩)
      (by intro p; cases p <;> rfl) (by intro p; cases p <;> rfl)

/-- Changing the depth allowance commutes with normalization. -/
theorem normalize_raise (n : Nat) {I O} (G : Hypernet ops n I O) :
    normalize ops (n+1) (raise ops n G) = Linear.raise ops n (normalize ops n G) := by
  induction n generalizing I O with
  | zero => rfl
  | succ n ih =>
    simp only [normalize,raise,Linear.raise,SetNet.relabel,SetNet.toNet,Net.relabel]
    congr 1
    funext e
    cases G.edgeLabel e with
    | inl p => rfl
    | inr b => exact congrArg (fun body => Sum.inr (⟨b.bound,b.free,body⟩ : Box (Linear.alphabet ops (n+1)))) (ih b.body)

/-- Recursive set isomorphisms normalize to recursive typed isomorphisms. -/
noncomputable def normalize_iso : (n : Nat) → {I O : List Wire} →
    {G H : Hypernet ops n I O} → DeepIso ops G H →
      Linear.DeepIso (normalize ops n G) (normalize ops n H)
  | 0,_,_,_,_,f => f.toNet
  | n+1,_,_,G,H,f => {
      vertices := f.interiors
      edges := f.edges
      internal_label := fun v => f.vertex_label v.val
      source := f.toNet.source
      target := f.toNet.target
      edge_label := by
        intro e
        have h := f.edge_label e
        cases a : G.edgeLabel e with
        | inl p => cases b : H.edgeLabel (f.edges.toFun e) with
          | inl q =>
            simp only [a,b,LabelEquiv] at h
            simpa only [normalize,Net.relabel,SetNet.toNet,a,b,Linear.LabelEquiv] using h
          | inr b => simp [a,b,LabelEquiv] at h
        | inr p => cases b : H.edgeLabel (f.edges.toFun e) with
          | inl q => simp [a,b,LabelEquiv] at h
          | inr q =>
            simp only [a,b,LabelEquiv] at h
            simp only [normalize,Net.relabel,SetNet.toNet,a,b,Linear.LabelEquiv]
            cases h with
            | bodies related =>
              obtain ⟨iso⟩ := related
              exact .bodies ⟨normalize_iso n iso⟩
    }

/-- Recursive typed isomorphisms expose to recursive set isomorphisms. -/
noncomputable def expose_iso : (n : Nat) → {I O : List Wire} →
    {G H : Linear.Hypernet ops n I O} → Linear.DeepIso G H →
      DeepIso ops (expose ops n G) (expose ops n H)
  | 0,_,_,G,H,f => {
      vertices := Port.bijection f.vertices
      edges := f.edges
      vertex_label := by intro v; cases v with
        | internal v => exact f.internal_label v
        | input i => rfl
        | output j => rfl
      edge_label := f.edge_label
      input := fun _ => rfl
      output := fun _ => rfl
      source := f.source
      target := f.target
    }
  | n+1,_,_,G,H,f => {
      vertices := Port.bijection f.vertices
      edges := f.edges
      vertex_label := by intro v; cases v with
        | internal v => exact f.internal_label v
        | input i => rfl
        | output j => rfl
      input := fun _ => rfl
      output := fun _ => rfl
      source := f.source
      target := f.target
      edge_label := by
        intro e
        have h := f.edge_label e
        cases a : G.edgeLabel e with
        | inl p => cases b : H.edgeLabel (f.edges.toFun e) with
          | inl q =>
            simp only [a,b,Linear.LabelEquiv] at h
            simpa only [expose,SetNet.relabel,Net.toSet,a,b,LabelEquiv] using h
          | inr b => simp [a,b,Linear.LabelEquiv] at h
        | inr p => cases b : H.edgeLabel (f.edges.toFun e) with
          | inl q => simp [a,b,Linear.LabelEquiv] at h
          | inr q =>
            simp only [a,b,Linear.LabelEquiv] at h
            simp only [expose,SetNet.relabel,Net.toSet,a,b,LabelEquiv]
            cases h with
            | bodies related =>
              obtain ⟨iso⟩ := related
              exact .bodies ⟨expose_iso n iso⟩
    }

/-- Exposure preserves and reflects isomorphism of typed hierarchies. -/
theorem expose_iso_iff (n : Nat) {I O} (G H : Linear.Hypernet ops n I O) :
    Nonempty (DeepIso ops (expose ops n G) (expose ops n H)) ↔ Nonempty (Linear.DeepIso G H) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨(typed_roundtrip ops n G).trans ((normalize_iso ops n f).trans (typed_roundtrip ops n H).symm)⟩
  · rintro ⟨f⟩; exact ⟨expose_iso ops n f⟩

/-- Repeated promotion embeds any smaller bound into a larger one. -/
noncomputable def raiseBy (n : Nat) : (k : Nat) → {I O : List Wire} → Hypernet ops n I O → Hypernet ops (n+k) I O
  | 0,_,_,G => G
  | k+1,_,_,G => raise ops (n+k) (raiseBy n k G)

/-- The analogous iterated promotion on the existing typed hierarchy. -/
noncomputable def typedRaiseBy (n : Nat) : (k : Nat) → {I O : List Wire} →
    Linear.Hypernet ops n I O → Linear.Hypernet ops (n+k) I O
  | 0,_,_,G => G
  | k+1,_,_,G => Linear.raise ops (n+k) (typedRaiseBy n k G)

/-- Normalization is coherent for arbitrary increases of the bound. -/
theorem normalize_raiseBy (n k : Nat) {I O} (G : Hypernet ops n I O) :
    normalize ops (n+k) (raiseBy ops n k G) = typedRaiseBy ops n k (normalize ops n G) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change normalize ops (n+k+1) (raise ops (n+k) (raiseBy ops n k G)) = _
    rw [normalize_raise,ih]; rfl

/-- A finite family of box contents may use independently chosen depth bounds. -/
structure BoxFamily (E : Type) where
  depth : E → Nat
  bound : E → Nat
  free : E → Nat
  body : ∀ e, Hypernet ops (depth e) [.term] (List.replicate (bound e + free e) .term)

/-- The maximum of a finite list of depth allowances (zero for an empty list). -/
def maximum : List Nat → Nat
  | [] => 0
  | n::ns => max n (maximum ns)

theorem le_maximum {ns : List Nat} {n : Nat} (mem : n ∈ ns) : n ≤ maximum ns := by
  induction ns with
  | nil => cases mem
  | cons a ns ih =>
    rcases List.mem_cons.mp mem with rfl | mem
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih mem) (Nat.le_max_right _ _)

/-- A common bound exists because the set of shallow box occurrences is finite. -/
def BoxFamily.common {E : Type} (F : BoxFamily ops E) (edges : Enumeration E) : Nat :=
  maximum (edges.elements.map F.depth)

theorem BoxFamily.le_common {E : Type} (F : BoxFamily ops E) (edges : Enumeration E) (e : E) :
    F.depth e ≤ F.common ops edges :=
  le_maximum (List.mem_map_of_mem (edges.complete e))

/-- Pad every member of a finite mixed-depth family to its common allowance. -/
noncomputable def BoxFamily.uniform {E : Type} (F : BoxFamily ops E) (edges : Enumeration E) (e : E) :
    Hypernet ops (F.common ops edges) [.term] (List.replicate (F.bound e + F.free e) .term) :=
  (Nat.add_sub_of_le (F.le_common ops edges e)) ▸
    raiseBy ops (F.depth e) (F.common ops edges - F.depth e) (F.body e)

/-- The typed result of uniformization is exactly promotion of the normalized
original member, even though the family had no uniform bound initially. -/
theorem BoxFamily.uniform_normalize {E : Type} (F : BoxFamily ops E) (edges : Enumeration E) (e : E) :
    normalize ops (F.common ops edges) (F.uniform ops edges e) =
      (Nat.add_sub_of_le (F.le_common ops edges e)) ▸
        typedRaiseBy ops (F.depth e) (F.common ops edges - F.depth e)
          (normalize ops (F.depth e) (F.body e)) := by
  have cast {a b : Nat} (eq : a = b) {I O} (G : Hypernet ops a I O) :
      normalize ops b (eq ▸ G) = eq ▸ normalize ops a G := by cases eq; rfl
  unfold BoxFamily.uniform
  rw [cast,normalize_raiseBy]

end Hypernets.Linear.SetHierarchy

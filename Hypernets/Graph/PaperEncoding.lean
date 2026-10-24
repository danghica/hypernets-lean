import Hypernets.Graph.NamedPresentation
import Hypernets.Graph.SetHierarchy
import Hypernets.Graph.RecursiveIsoPlug

/-! Graph-valued box labels without stored binder annotations. Binder counts
are read from ordinary input-vertex names after a proved bijective freshening. -/
namespace Hypernets.Linear.PaperEncoding
open Graph
variable {Op : Type} (ops : Operations Op)

/-- A graph body with its actual number of term outputs. This is part of its
ordered interface, not an annotation of the enclosing box. -/
abbrev Body (A : Alphabet) := Σ n : Nat, NamedNet A.signature [.term] (List.replicate n .term)

/-- Read two coordinates of the sole input vertex's ordinary name. -/
def bound {A : Alphabet} (body : Body A) : Nat := (body.2.input 0).val.1
def free {A : Alphabet} (body : Body A) : Nat := (body.2.input 0).val.2.1

/-- Admissible graph-valued labels. The sole stored datum is a graph body;
the proof checks the UAM box discipline against its boundary names. -/
abbrev Content (A : Alphabet) := {body : Body A // bound body + free body = body.1}

/-- Boxes are labelled by contents; no separate binder-count fields occur. -/
def nextAlphabet (A : Alphabet) : Alphabet where
  Symbol := Primitive Op ⊕ Content A
  signature := {
    input | .inl p => (primitiveSignature ops).input p | .inr c => [.thunk (bound c.val)]
    output | .inl p => (primitiveSignature ops).output p | .inr c => List.replicate (free c.val) .term
  }

@[reducible] def alphabet : Nat → Alphabet
  | 0 => baseAlphabet ops
  | n+1 => nextAlphabet ops (alphabet n)

abbrev Hypernet (n : Nat) (I O : List Wire) := NamedNet (alphabet ops n).signature I O

/-- Equality of the actual contents forces equality of the complete external
signature. Proof fields carry no extra label information. -/
theorem same_content_signature {A : Alphabet} (c d : Content A) (eq : c.val = d.val) :
    (nextAlphabet ops A).signature.input (.inr c) = (nextAlphabet ops A).signature.input (.inr d) ∧
    (nextAlphabet ops A).signature.output (.inr c) = (nextAlphabet ops A).signature.output (.inr d) := by
  have same : c = d := Subtype.ext eq
  subst d
  exact ⟨rfl,rfl⟩

/-- A signature-preserving translation of alphabets. -/
structure AlphabetMap (A B : Alphabet) where
  symbol : A.Symbol → B.Symbol
  input : ∀ p, B.signature.input (symbol p) = A.signature.input p
  output : ∀ p, B.signature.output (symbol p) = A.signature.output p

/-- Recursively replace each annotated box by its freshly named actual contents. -/
noncomputable def encodeMap : (n : Nat) → AlphabetMap (Linear.alphabet ops n) (alphabet ops n)
  | 0 => ⟨id,fun _ => rfl,fun _ => rfl⟩
  | n+1 => {
      symbol p := match p with
        | .inl p => .inl p
        | .inr b => .inr ⟨⟨b.bound+b.free,
            NamedNet.ofSet (b.body.toSet.relabel _ (encodeMap n).symbol
              (encodeMap n).input (encodeMap n).output) b.bound b.free⟩,rfl⟩
      input := by intro p; cases p <;> rfl
      output := by intro p; cases p <;> rfl
    }

/-- Translate and freshly name a whole hypernet. The chosen outer prefix is
arbitrary; only prefixes at box contents determine their enclosing signatures. -/
noncomputable def encode (n a b : Nat) {I O} (G : Linear.Hypernet ops n I O) : Hypernet ops n I O :=
  NamedNet.ofSet (G.toSet.relabel _ (encodeMap ops n).symbol
    (encodeMap ops n).input (encodeMap ops n).output) a b

/-- Decode graph-valued labels by reading their external counts from vertex
names and normalizing their contents. The admissibility proof supplies the
body's required ordered interface. -/
noncomputable def decodeMap : (n : Nat) → AlphabetMap (alphabet ops n) (Linear.alphabet ops n)
  | 0 => ⟨id,fun _ => rfl,fun _ => rfl⟩
  | n+1 => {
      symbol p := match p with
        | .inl p => .inl p
        | .inr c => .inr ⟨bound c.val,free c.val,
            c.property.symm ▸ c.val.2.toSet.toNet.relabel _ (decodeMap n).symbol
              (decodeMap n).input (decodeMap n).output⟩
      input := by intro p; cases p <;> rfl
      output := by intro p; cases p <;> rfl
    }

noncomputable def decode (n : Nat) {I O} (G : Hypernet ops n I O) : Linear.Hypernet ops n I O :=
  G.toSet.toNet.relabel _ (decodeMap ops n).symbol (decodeMap ops n).input (decodeMap ops n).output

/-- The chosen prefix appears literally in every encoded input's vertex name. -/
theorem encode_prefix (n a b : Nat) {I O} (G : Linear.Hypernet ops n I O) (i : Fin I.length) :
    ((encode ops n a b G).input i).val.1 = a ∧
    ((encode ops n a b G).input i).val.2.1 = b := ⟨rfl,rfl⟩

/-- Every typed hypernet survives encoding and decoding up to recursive
isomorphism, for every choice of its outer name prefix. -/
noncomputable def roundtrip : (n : Nat) → (a b : Nat) → {I O : List Wire} →
    (G : Linear.Hypernet ops n I O) → Linear.DeepIso G (decode ops n (encode ops n a b G))
  | 0,a,b,_,_,G => Linear.DeepIso.ofIso (NamedNet.typed_roundtrip G a b)
  | n+1,a,b,_,_,G => {
      vertices := (NamedNet.typed_roundtrip G a b).vertices
      edges := (NamedNet.typed_roundtrip G a b).edges
      internal_label := (NamedNet.typed_roundtrip G a b).internal_label
      source := (NamedNet.typed_roundtrip G a b).source
      target := (NamedNet.typed_roundtrip G a b).target
      edge_label := by
        intro e
        change Linear.LabelEquiv ops (n+1) (G.edgeLabel e)
          ((decodeMap ops (n+1)).symbol ((encodeMap ops (n+1)).symbol (G.edgeLabel e)))
        cases G.edgeLabel e with
        | inl p => rfl
        | inr c => exact .bodies ⟨roundtrip n c.bound c.free c.body⟩
    }

/-- Any property invariant under recursive graph isomorphism survives the
complete representation round trip. No operational property is postulated. -/
theorem roundtrip_property (n a b : Nat) {I O} (G : Linear.Hypernet ops n I O)
    (P : Linear.Hypernet ops n I O → Prop)
    (invariant : ∀ {G H}, Linear.DeepIso G H → (P G ↔ P H)) :
    P G ↔ P (decode ops n (encode ops n a b G)) := invariant (roundtrip ops n a b G)

/-- Recursive comparison of actual graph-valued labels. Counts are read from
names and compared as external signatures; bodies are compared as ordered graphs. -/
def LabelEquiv : (n : Nat) → (alphabet ops n).Symbol → (alphabet ops n).Symbol → Prop
  | 0,p,q => p = q
  | _+1,.inl p,.inl q => p = q
  | n+1,.inr c,.inr d => bound c.val = bound d.val ∧ free c.val = free d.val ∧
      Nonempty (SetNet.HRelIso (LabelEquiv n) c.val.2.toSet d.val.2.toSet)
  | _+1,_,_ => False

abbrev DeepIso {n I O I' O'} (G : Hypernet ops n I O) (H : Hypernet ops n I' O') :=
  SetNet.HRelIso (LabelEquiv ops n) G.toSet H.toSet

/-- Decode followed by encoding preserves every graph in the named-content
presentation, including its ordered boundaries and nested contents. -/
noncomputable def named_roundtrip : (n : Nat) → (a b : Nat) → {I O : List Wire} →
    (G : Hypernet ops n I O) → DeepIso ops G (encode ops n a b (decode ops n G))
  | 0,a,b,_,_,G => NamedNet.roundtrip G a b
  | n+1,a,b,_,_,G => {
      vertices := (NamedNet.roundtrip G a b).vertices
      edges := (NamedNet.roundtrip G a b).edges
      vertex_label := (NamedNet.roundtrip G a b).vertex_label
      input := (NamedNet.roundtrip G a b).input
      output := (NamedNet.roundtrip G a b).output
      source := (NamedNet.roundtrip G a b).source
      target := (NamedNet.roundtrip G a b).target
      edge_label := by
        intro e
        change LabelEquiv ops (n+1) (G.edgeLabel e)
          ((encodeMap ops (n+1)).symbol ((decodeMap ops (n+1)).symbol (G.edgeLabel e)))
        cases G.edgeLabel e with
        | inl p => rfl
        | inr c =>
          refine ⟨rfl,rfl,?_⟩
          have body {r s : Nat} (h : r = s) (H : Hypernet ops n [.term] (List.replicate r .term)) :
              Nonempty (DeepIso ops H
                (encode ops n (bound c.val) (free c.val) (h ▸ decode ops n H))) := by
            cases h
            exact ⟨named_roundtrip n (bound c.val) (free c.val) H⟩
          exact body c.property.symm c.val.2
    }

/-- Encoding preserves recursive isomorphisms even with independently chosen
outer name prefixes. The labels remain actual contents throughout. -/
noncomputable def encode_iso (n : Nat) (a b c d : Nat) {I O}
    {G H : Linear.Hypernet ops n I O} (f : Linear.DeepIso G H) :
    DeepIso ops (encode ops n a b G) (encode ops n c d H) := by
  induction n generalizing I O a b c d with
  | zero => exact NamedNet.map_iso f.toSet a b c d
  | succ n ih =>
    apply NamedNet.map_iso (f.toSet.relabel _ (encodeMap ops (n+1)).symbol
      (encodeMap ops (n+1)).input (encodeMap ops (n+1)).output (LabelEquiv ops (n+1)) ?_) a b c d
    intro p q h
    cases p with
    | inl p => cases q with
      | inl q => exact h
      | inr q => exact False.elim h
    | inr p => cases q with
      | inl q => exact False.elim h
      | inr q =>
        cases h with
        | bodies related =>
          obtain ⟨body⟩ := related
          exact ⟨rfl,rfl,⟨ih _ _ _ _ body⟩⟩

/-- Decoding preserves recursive ordered-graph isomorphisms. In the box case,
interface transports are eliminated only after the external counts agree. -/
noncomputable def decode_iso (n : Nat) {I O} {G H : Hypernet ops n I O}
    (f : DeepIso ops G H) : Linear.DeepIso (decode ops n G) (decode ops n H) := by
  induction n generalizing I O with
  | zero => exact f.same.toNet
  | succ n ih =>
    have bodies {r s b c b' c' : Nat} (hb : b = b') (hc : c = c')
        (P : Hypernet ops n [.term] (List.replicate r .term))
        (Q : Hypernet ops n [.term] (List.replicate s .term))
        (hp : b+c = r) (hq : b'+c' = s) (related : DeepIso ops P Q) :
        Linear.LabelEquiv ops (n+1)
          (.inr ⟨b,c,hp.symm ▸ decode ops n P⟩)
          (.inr ⟨b',c',hq.symm ▸ decode ops n Q⟩) := by
      cases hb; cases hc; cases hp; cases hq
      exact .bodies ⟨ih related⟩
    exact {
      vertices := f.same.toNet.vertices
      edges := f.edges
      internal_label := f.same.toNet.internal_label
      source := f.same.toNet.source
      target := f.same.toNet.target
      edge_label := by
        intro e
        change Linear.LabelEquiv ops (n+1)
          ((decodeMap ops (n+1)).symbol (G.edgeLabel e))
          ((decodeMap ops (n+1)).symbol (H.edgeLabel (f.edges.toFun e)))
        have h := f.edge_label e
        cases ep : G.edgeLabel e with
        | inl p => cases eq : H.edgeLabel (f.edges.toFun e) with
          | inl q => simpa only [ep,eq,LabelEquiv,decodeMap,Linear.LabelEquiv] using h
          | inr q => simp [ep,eq,LabelEquiv] at h
        | inr p => cases eq : H.edgeLabel (f.edges.toFun e) with
          | inl q => simp [ep,eq,LabelEquiv] at h
          | inr q =>
            simp only [ep,eq,LabelEquiv] at h
            obtain ⟨hb,hf,⟨rel⟩⟩ := h
            exact bodies hb hf p.val.2 q.val.2 p.property q.property rel
    }

/-- Encoding is faithful as well as preserving isomorphism. -/
theorem encode_iso_iff (n a b c d : Nat) {I O} (G H : Linear.Hypernet ops n I O) :
    Nonempty (DeepIso ops (encode ops n a b G) (encode ops n c d H)) ↔ Nonempty (Linear.DeepIso G H) := by
  constructor
  · rintro ⟨f⟩
    exact ⟨(roundtrip ops n a b G).trans ((decode_iso ops n f).trans (roundtrip ops n c d H).symm)⟩
  · rintro ⟨f⟩; exact ⟨encode_iso ops n a b c d f⟩

/-- Actual-content label equivalence is reflexive at every depth. -/
theorem label_refl (n : Nat) (p : (alphabet ops n).Symbol) : LabelEquiv ops n p p := by
  induction n with
  | zero => rfl
  | succ n ih =>
    cases p with
    | inl p => rfl
    | inr p => exact ⟨rfl,rfl,⟨SetNet.HRelIso.refl ih p.val.2.toSet⟩⟩

theorem label_symm (n : Nat) {p q : (alphabet ops n).Symbol}
    (h : LabelEquiv ops n p q) : LabelEquiv ops n q p := by
  induction n with
  | zero => exact h.symm
  | succ n ih =>
    cases p with
    | inl p => cases q with
      | inl q => exact h.symm
      | inr q => exact False.elim h
    | inr p => cases q with
      | inl q => exact False.elim h
      | inr q =>
        obtain ⟨hb,hf,⟨f⟩⟩ := h
        exact ⟨hb.symm,hf.symm,⟨f.symm (fun h => ih h)⟩⟩

theorem label_trans (n : Nat) {p q r : (alphabet ops n).Symbol}
    (h : LabelEquiv ops n p q) (k : LabelEquiv ops n q r) : LabelEquiv ops n p r := by
  induction n with
  | zero => exact h.trans k
  | succ n ih =>
    cases p with
    | inl p => cases q with
      | inl q => cases r with
        | inl r => exact h.trans k
        | inr r => exact False.elim k
      | inr q => exact False.elim h
    | inr p => cases q with
      | inl q => exact False.elim h
      | inr q => cases r with
        | inl r => exact False.elim k
        | inr r =>
          obtain ⟨hb,hf,⟨f⟩⟩ := h
          obtain ⟨kb,kf,⟨g⟩⟩ := k
          exact ⟨hb.trans kb,hf.trans kf,⟨f.trans (fun h k => ih h k) g⟩⟩

/-- The actual-content presentation modulo recursive, typed graph isomorphism. -/
def setoid (n : Nat) (I O : List Wire) : Setoid (Hypernet ops n I O) where
  r G H := Nonempty (DeepIso ops G H)
  iseqv := {
    refl G := ⟨SetNet.HRelIso.refl (label_refl ops n) G.toSet⟩
    symm := fun ⟨f⟩ => ⟨f.symm (label_symm ops n)⟩
    trans := fun ⟨f⟩ ⟨g⟩ => ⟨f.trans (label_trans ops n) g⟩
  }

abbrev Class (n : Nat) (I O : List Wire) := Quotient (setoid ops n I O)

/-- Encoding is well-defined on the existing recursive-isomorphism quotient. -/
noncomputable def encodeClass (n : Nat) (I O : List Wire) :
    Quotient (Linear.deepSetoid ops n I O) → Class ops n I O :=
  Quotient.lift (fun G => Quotient.mk _ (encode ops n 0 0 G))
    (fun _ _ ⟨f⟩ => Quotient.sound ⟨encode_iso ops n 0 0 0 0 f⟩)

/-- Decoding is well-defined on actual-content isomorphism classes. -/
noncomputable def decodeClass (n : Nat) (I O : List Wire) :
    Class ops n I O → Quotient (Linear.deepSetoid ops n I O) :=
  Quotient.lift (fun G => Quotient.mk _ (decode ops n G))
    (fun _ _ ⟨f⟩ => Quotient.sound ⟨decode_iso ops n f⟩)

/-- Decoding after encoding is the identity on the existing graph quotient. -/
theorem decode_encodeClass (n : Nat) (I O : List Wire)
    (x : Quotient (Linear.deepSetoid ops n I O)) :
    decodeClass ops n I O (encodeClass ops n I O x) = x := by
  induction x using Quotient.inductionOn with
  | h G => exact (Quotient.sound (s := Linear.deepSetoid ops n I O) ⟨roundtrip ops n 0 0 G⟩).symm

/-- Encoding after decoding is the identity on actual-content graph classes. -/
theorem encode_decodeClass (n : Nat) (I O : List Wire) (x : Class ops n I O) :
    encodeClass ops n I O (decodeClass ops n I O x) = x := by
  induction x using Quotient.inductionOn with
  | h G => exact (Quotient.sound (s := setoid ops n I O) ⟨named_roundtrip ops n 0 0 G⟩).symm

/-- All predicates on graph classes, not only a selected list of invariants,
transport across the representation without change of truth value. -/
theorem class_property (n : Nat) (I O : List Wire)
    (P : Quotient (Linear.deepSetoid ops n I O) → Prop) (x) :
    P (decodeClass ops n I O (encodeClass ops n I O x)) ↔ P x := by
  rw [decode_encodeClass]

/-- Relations on graph classes transport as well; this includes any already
established isomorphism-invariant context or transition relation. -/
theorem class_relation (n : Nat) (I O : List Wire)
    (R : Quotient (Linear.deepSetoid ops n I O) → Quotient (Linear.deepSetoid ops n I O) → Prop) (x y) :
    R (decodeClass ops n I O (encodeClass ops n I O x))
      (decodeClass ops n I O (encodeClass ops n I O y)) ↔ R x y := by
  rw [decode_encodeClass,decode_encodeClass]

/-- The literal label data: primitives or actual graph bodies. The subtype's
admissibility proof is omitted; no binder annotation is retained. -/
def bareLabel (n : Nat) : (alphabet ops (n+1)).Symbol → Primitive Op ⊕ Body (alphabet ops n)
  | .inl p => .inl p
  | .inr c => .inr c.val

/-- The proof carried by a content label adds no information to its literal graph data. -/
theorem bareLabel_injective (n : Nat) {p q : (alphabet ops (n+1)).Symbol}
    (eq : bareLabel ops n p = bareLabel ops n q) : p = q := by
  cases p with
  | inl p => cases q with
    | inl q => exact congrArg Sum.inl (Sum.inl.inj eq)
    | inr q => cases eq
  | inr p => cases q with
    | inl q => cases eq
    | inr q => exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj eq))

/-- Paper §3.1(3), explicitly for the literal undecorated labels of each encoded
or otherwise admissible named graph. Equal labels have equal incidence types. -/
theorem equal_labels_same_types (n : Nat) {I O} (G : Hypernet ops (n+1) I O)
    (e f : G.Edge) (eq : bareLabel ops n (G.edgeLabel e) = bareLabel ops n (G.edgeLabel f)) :
    (G.source e).map G.vertexLabel = (G.source f).map G.vertexLabel ∧
    (G.target e).map G.vertexLabel = (G.target f).map G.vertexLabel := by
  have labels := bareLabel_injective ops n eq
  constructor
  · rw [G.source_typed,G.source_typed,labels]
  · rw [G.target_typed,G.target_typed,labels]

/-- The apparent output count in a body package is exactly the number of its
ordered output vertices; it is not extra data describing the enclosing box. -/
theorem body_output_length {A : Alphabet} (body : Body A) :
    (List.ofFn body.2.output).length = body.1 := by simp

/-- Every existing typed graph has an actual-content representative, with no
body-consistency hypothesis or restriction on the existing graph class. -/
theorem representable (n : Nat) {I O} (G : Linear.Hypernet ops n I O) :
    ∃ H : Hypernet ops n I O, Nonempty (Linear.DeepIso G (decode ops n H)) :=
  ⟨encode ops n 0 0 G,⟨roundtrip ops n 0 0 G⟩⟩

end Hypernets.Linear.PaperEncoding

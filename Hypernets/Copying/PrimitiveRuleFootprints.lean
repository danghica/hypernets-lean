import Hypernets.Copying.BPermPathClassification

/-! All basic-operation footprints are primitive, with the original stable
premises. Only beta and copying may inspect boxes in a local rewrite. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPermutation.PrimitiveFootprint
open Graph

theorem primitive (d : Nat) (p : Primitive) : PrimitiveFootprint (primitiveNet d p) := by
  cases d <;> exact fun _ => ⟨p,rfl⟩

theorem relabel {I O} (G : Net primitiveSignature I O) (d : Nat) :
    PrimitiveFootprint (G.relabel (alphabet d).signature (primitiveLabel d) (primitive_input d) (primitive_output d)) :=
  fun e => ⟨G.edgeLabel e,rfl⟩

theorem stable {d O} {G : Hypernet d [.term] O} (h : Stable G) : PrimitiveFootprint G := by
  intro e; obtain ⟨p,label,_⟩ := h.labels e; exact ⟨p,label⟩

theorem expand {d I O} (C : Hypernet d I O) {F}
    (all : ∀ e, PrimitiveFootprint (F e)) : PrimitiveFootprint (C.expand F) :=
  fun e => all e.1 e.2

theorem serial {d I J K} {G : Hypernet d I J} {H : Hypernet d J K}
    (g : PrimitiveFootprint G) (h : PrimitiveFootprint H) : PrimitiveFootprint (Serial.net G H) := by
  apply expand
  intro b; cases d <;> cases b <;> assumption

theorem tensor {d I O J K} {G : Hypernet d I O} {H : Hypernet d J K}
    (g : PrimitiveFootprint G) (h : PrimitiveFootprint H) : PrimitiveFootprint (Net.Tensor.net G H) := by
  rintro ⟨b,e⟩; cases b
  · exact g e
  · exact h e

theorem allocation {d O} (G : Hypernet d [.term] O) (h : Stable G) :
    PrimitiveFootprint (Allocation.before G) := serial (primitive _ _) (stable h)

theorem assignment {d h O} (T : ContractionTree .atom (h+1)) (G : Hypernet d [.term] O) (hG : Stable G) :
    PrimitiveFootprint (Assignment.before T G) := by
  apply expand
  intro e; cases d <;> cases e
  all_goals first | exact stable hG | exact primitive _ _ | exact relabel _ _

theorem dereference {h} (T : ContractionTree .atom (h+1)) (d : Nat) :
    PrimitiveFootprint (Dereference.before T d) := relabel _ _

theorem same {h} (T : ContractionTree .atom (h+2)) (d : Nat) :
    PrimitiveFootprint (AtomEquality.Same.before T d) := relabel _ _

theorem different {n m} (T : ContractionTree .atom (n+1)) (U : ContractionTree .atom (m+1)) (d : Nat) :
    PrimitiveFootprint (AtomEquality.Different.before T U d) := relabel _ _

theorem unary (d n : Nat) : PrimitiveFootprint (Arithmetic.unaryBefore d n) :=
  serial (primitive _ _) (primitive _ _)

theorem binary (o : Arithmetic.BinaryCode) (d m n : Nat) : PrimitiveFootprint (Arithmetic.binaryBefore o d m n) :=
  serial (primitive _ _) (tensor (primitive _ _) (primitive _ _))
end Hypernets.Copying.BoxPermutation.PrimitiveFootprint

namespace Hypernets.Copying.Combined
open Graph MatchEmbedding BoxPermutation

/-- Exact exhaustive classification of the original local rule constructors. -/
theorem Local.footprint_cases {d I O} {G H : Hypernet d I O} {v w} (step : Local G v H w) :
    PrimitiveFootprint G ∨ (∃ e, HeadAt G v e (.operation .app)) ∨
      ∃ e, HeadAt G v e (.contraction .term) := by
  cases step with
  | allocate G h => exact .inl (PrimitiveFootprint.allocation G h)
  | read T d => exact .inl (PrimitiveFootprint.dereference T d)
  | assign T G h => exact .inl (PrimitiveFootprint.assignment T G h)
  | same T d => exact .inl (PrimitiveFootprint.same T d)
  | different T U d => exact .inl (PrimitiveFootprint.different T U d)
  | unaryArithmetic d n => exact .inl (PrimitiveFootprint.unary d n)
  | binaryArithmetic o d m n => exact .inl (PrimitiveFootprint.binary o d m n)
  | beta B G h => exact .inr (.inl ⟨_,(Application.localMatch B G).head_at⟩)
  | copy T G h => exact .inr (.inr (CopyRule.before_active_head T G _))

/-- Extract an actual local rule occurrence from any nested plug/expansion and
renaming derivation. No transition or complement is invented by this extraction. -/
theorem Rewrite.local_source {d I O} {G H : Hypernet d I O} {v w} (step : Rewrite G v H w) :
    ∃ J K, ∃ A B : Hypernet d J K, ∃ a b, Local A a B b ∧
      ∃ f : MatchEmbedding A G, f.ports a = v := by
  induction step with
  | «local» h => exact ⟨_,_,_,_,_,_,h,MatchEmbedding.refl _,rfl⟩
  | rename f g step ih =>
    obtain ⟨J,K,A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K,A,B,a,b,h,q.comp (MatchEmbedding.ofDeepIso f),congrArg (Port.map f.vertices.toFun) eq⟩
  | plug C e step ih =>
    obtain ⟨J,K,A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K,A,B,a,b,h,q.comp (MatchEmbedding.plug C e _),congrArg (Net.Replacement.insert C e _) eq⟩
  | expand C F K e others step ih =>
    obtain ⟨J,K',A,B,a,b,h,q,eq⟩ := ih
    exact ⟨J,K',A,B,a,b,h,q.comp (MatchEmbedding.expand C F e),congrArg (Net.Expansion.insert C F e) eq⟩
end Hypernets.Copying.Combined

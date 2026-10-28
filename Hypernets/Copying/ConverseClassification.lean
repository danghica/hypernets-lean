import Hypernets.Copying.ConversePrimitiveOverlap
import Hypernets.Copying.ConverseBetaOverlap
import Hypernets.Copying.ConverseStoreOverlap

/-! Exhaustive converse classification of the actual contextual machine rule.
Changed data and selected spines are reflected without claiming that an
irrelevant sibling in an arbitrarily large supplied tree is a retained edge. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.OperationalTemplates.ConverseOverlap
open Graph Search.Expansion MatchEmbedding Combined

/-- Every branch retains a certificate identifying the actual supplied
whole successor, including its resumed token. -/
inductive Case {kind : Kind} {d I O} (C : Hypernet d I O)
    (L R : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))) (v : C.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) : Prop where
  | retained {J K} {A B : Hypernet d J K} {a b}
      (localStep : Local A a B b) (occurrence : Opening.Occurrence A (C.expand R))
      (token : occurrence.ports a = Net.Expansion.host C R v)
      (avoid : RetainedFootprint.AvoidsShallow C occurrence.matchEmbedding)
      (successor : Nonempty (StateIso ⟨H,(.search,w)⟩
        ⟨CompleteMatchCut.replaceWith occurrence.matchEmbedding occurrence.label B,
          (.search,CompleteMatchCut.replacePort occurrence.matchEmbedding occurrence.label B b)⟩)) :
      Case (kind := kind) C L R v H w
  | read (actual : Dereference.Match (C.expand R) (Net.Expansion.host C R v))
      (original : Dereference.Match C v)
      (head : original.headEdge = actual.headEdge.1) (store : original.storeEdge = actual.storeEdge.1)
      (count : original.count = actual.count)
      (contents : Net.Expansion.host C R original.contents = actual.contents)
      (successor : Nonempty (StateIso actual.canonical ⟨H,(.search,w)⟩)) : Case (kind := kind) C L R v H w
  | assign (actual : Assignment.Match (C.expand R) (Net.Expansion.host C R v))
      (original : Assignment.Match C v)
      (head : original.headEdge = actual.headEdge.1) (store : original.storeEdge = actual.storeEdge.1)
      (count : original.count = actual.count)
      (instancePort : Net.Expansion.host C R original.instanceWire = actual.instanceWire)
      (newValue : Net.Expansion.host C R original.newValue = actual.newValue)
      (oldValue : Net.Expansion.host C R original.oldValue = actual.oldValue)
      (successor : Nonempty (StateIso actual.canonical ⟨H,(.search,w)⟩)) : Case (kind := kind) C L R v H w
  | equality {e b} (head : HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation (.binary .atomEq)))
      (actual : AtomEquality.Decision (C.expand R) (Net.Expansion.host C R v) b)
      (original : AtomEquality.Decision C v b)
      (successor : Nonempty (StateIso (AtomEquality.canonical (C.expand R) e head.1
        (Net.Expansion.host C R v) b) ⟨H,(.search,w)⟩)) : Case (kind := kind) C L R v H w
  | copy {k h} {P : Hypernet d [.term] (environmentInterface k h)}
      (actual : CopyRule.SuccessorCertificate (C.expand R) H (Net.Expansion.host C R v) w P)
      (payload : RetainedFootprint.AvoidsShallow C actual.matched.payload.matchEmbedding)
      (resolution : ∃ n, CopyTrace.Resolves C v (actual.matched.payload.edges actual.matched.normal.head).1
        actual.matched.normal.primitive n) : Case (kind := kind) C L R v H w

variable {kind d I O} (C : Hypernet d I O) {L R}
    (cert : ∀ e, DeepFillingEdge (template kind) C L R e)
    (free : BindingFree C) {input v} (away : ¬ Entering C (.rewrite,v))
    (rooted : Search.RootedFrom (C.expand L) input (.rewrite,Net.Expansion.host C L v))
    {H : Hypernet d I O} {w} (step : Rewrite (C.expand R) (Net.Expansion.host C R v) H w)
include cert free away rooted step

/-- An arbitrary actual read has its original source match and its complete
source-determined successor, independently of its supplied atom tree. -/
theorem classify_read {e} (head : HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation (.unary .deref))) :
    Case (kind := kind) C L R v H w := by
  obtain ⟨m⟩ := rewrite_dereference_match step head
  obtain ⟨q,h,s,n,c⟩ := read_match_owner C cert free away rooted m
  exact .read m q h s n c (rewrite_dereference_canonical step m)

/-- An arbitrary actual write has its original ordered ports and source match. -/
theorem classify_assignment {e} (head : HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation (.binary .assign))) :
    Case (kind := kind) C L R v H w := by
  obtain ⟨m⟩ := rewrite_assignment_match step head
  obtain ⟨q,h,s,n,a,b,c⟩ := assignment_match_owner C cert free away rooted m
  exact .assign m q h s n a b c (rewrite_assignment_canonical step m)

/-- Both equality rules reflect their actual decision and complete successor. -/
theorem classify_equality {e} (head : HeadAt (C.expand R) (Net.Expansion.host C R v) e (.operation (.binary .atomEq))) :
    Case (kind := kind) C L R v H w := by
  obtain ⟨b,decision⟩ := rewrite_equality_decision step head
  exact .equality head decision (equality_owner C cert free away rooted decision)
    (rewrite_equality_canonical step head decision)

omit rooted in
/-- The original copy certificate preserves the complete payload and exact
selected sharing spine while leaving unused sibling branches unrestricted. -/
theorem classify_copy {e} (head : HeadAt (C.expand R) (Net.Expansion.host C R v) e (.contraction .term)) :
    Case (kind := kind) C L R v H w := by
  cases rewrite_copy_certificate step ⟨e,head⟩ with
  | certificate actual =>
    apply Case.copy actual
    · exact fun e h => BindingOverlap.copying_payload_not_hole C (fun e => (cert e).converse) free away actual.matched e h
    · obtain ⟨n,resolve⟩ := actual.matched.resolves
      exact ⟨n,BindingOverlap.copying_resolution_owner C (fun e => (cert e).converse)
        free away actual.matched.head_at resolve⟩

/-- Every original local/rename/plug/expand rewrite is classified, with no
assumed overlap or residual certificate. All nine local constructors occur. -/
theorem rewrite_classification : Case (kind := kind) C L R v H w := by
  obtain ⟨J,K,A,B,a,b,localStep,f,attached⟩ := step.local_occurrence
  have head_at {e p} (head : HeadAt A a e p) :
      HeadAt (C.expand R) (Net.Expansion.host C R v) (f.edges e) p := by
    rw [← attached]; exact f.matchEmbedding.head head
  have successor := f.rewrite_successor (.local localStep) (by rw [attached]; exact step)
  cases localStep with
  | allocate G stable =>
    exact .retained (.allocate G stable) f attached (allocation_avoids C cert away rooted G stable f attached) successor
  | read T d => exact classify_read C cert free away rooted step (head_at (Dereference.localMatch T d).head)
  | assign T G stable => exact classify_assignment C cert free away rooted step (head_at (Assignment.localMatch T G).head)
  | same T d => exact classify_equality C cert free away rooted step (head_at (AtomEquality.Same.head_at T d))
  | different T U d => exact classify_equality C cert free away rooted step (head_at (AtomEquality.Different.head_at T U d))
  | unaryArithmetic d n =>
    exact .retained (.unaryArithmetic d n) f attached (unary_avoids C cert away rooted n f attached) successor
  | binaryArithmetic o d m n =>
    exact .retained (.binaryArithmetic o d m n) f attached (binary_avoids C cert away rooted o m n f attached) successor
  | beta B G stable =>
    exact .retained (.beta B G stable) f attached (beta_avoids C cert away rooted B G stable f attached) successor
  | copy T G copyable =>
    obtain ⟨e,head⟩ := CopyRule.before_active_head T G ⟨0,by simp⟩
    exact classify_copy C cert free away step (head_at head)

end Hypernets.Copying.OperationalTemplates.ConverseOverlap

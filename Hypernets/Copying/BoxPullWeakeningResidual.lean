import Hypernets.Copying.BoxPullWeakeningCopyCorrection
import Hypernets.Copying.DerivationFillings
import Hypernets.Copying.PointedFillingTransport

/-! Residuals keep the original BPullW filling separate from its two proved
Idem corrections. No transitivity of the original filling relation is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.BoxPullWeakening
open Graph Combined

/-- An original filling with its actual common-context token. -/
structure PointedWitness (T : PreTemplate) {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  filling : FillingWitness T G H
  point : filling.context.Vertex
  left : (filling.leftPosition (.search,point)).2 = v
  right : (filling.rightPosition (.search,point)).2 = w

namespace PointedWitness
variable {T : PreTemplate}
def input {d I O} {G H : Hypernet d I O} (w : FillingWitness T G H) (i : Fin I.length) :
    PointedWitness T G (.input i) H (.input i) := ⟨w,.input i,rfl,rfl⟩

def refl {d I O} (G : Hypernet d I O) (free : FocusFree G) (v : G.Vertex) :
    PointedWitness T G v G v := by
  refine ⟨FillingWitness.refl G free,v,?_,?_⟩ <;> cases v <;> rfl

def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : PointedWitness T G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    PointedWitness T A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) where
  filling := p.filling.congr f g
  point := p.point
  left := by
    change Port.map (n := I.length) (m := O.length) (f.vertices.toFun ∘ p.filling.leftIso.vertices.toFun)
      (Net.Expansion.host p.filling.context p.filling.left p.point) = _
    calc
      _ = Port.map f.vertices.toFun (p.filling.leftPosition (.search,p.point)).2 := by cases p.point <;> rfl
      _ = _ := congrArg (Port.map f.vertices.toFun) p.left
  right := by
    change Port.map (n := I.length) (m := O.length) (g.vertices.toFun ∘ p.filling.rightIso.vertices.toFun)
      (Net.Expansion.host p.filling.context p.filling.right p.point) = _
    calc
      _ = Port.map g.vertices.toFun (p.filling.rightPosition (.search,p.point)).2 := by cases p.point <;> rfl
      _ = _ := congrArg (Port.map g.vertices.toFun) p.right

def expandAt {d I O} (C : Hypernet d I O)
    {G H : (e : C.Edge) → Hypernet d ((alphabet d).signature.input (C.edgeLabel e))
      ((alphabet d).signature.output (C.edgeLabel e))}
    (w : ∀ e, FillingWitness T (G e) (H e)) (e : C.Edge) (v : (w e).context.Vertex) :
    PointedWitness T (C.expand G) (Net.Expansion.insert C G e ((w e).leftPosition (.search,v)).2)
      (C.expand H) (Net.Expansion.insert C H e ((w e).rightPosition (.search,v)).2) where
  filling := FillingWitness.expand C w
  point := Net.Expansion.insert C (fun e => (w e).context) e v
  left := congrArg Prod.snd (FillingWitness.expand_selected_leftPosition C w .search e v)
  right := congrArg Prod.snd (FillingWitness.expand_selected_rightPosition C w .search e v)

theorem label {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness T G v H w) : p.filling.context.vertexLabel p.point = G.vertexLabel v := by
  have eq := p.filling.leftPosition_label .search p.point
  rw [p.left] at eq
  exact eq.symm

/-- Every Idem intermediate is hole-free whenever either actual endpoint is. -/
theorem idem_holeFree {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness ContractionIdempotence.template G v H w) : HoleFree G ↔ HoleFree H :=
  p.filling.allLabels_iff (T := ContractionIdempotence.template) _ (fun pair => ⟨fun _ => pair.holeFree.2,fun _ => pair.holeFree.1⟩)

/-- The pointed exact correction also transports the actual original search
root. This interface is independent of any BPullW robustness premise. -/
theorem idem_exact {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness ContractionIdempotence.template G v H w)
    (closed : HoleFree G) (typed : G.vertexLabel v = .term)
    (root : StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩)) :
    StateClass.machine.Equiv CostOrder.exact
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) ∧
    StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  have lr : StateClass.Rooted (StateClass.ofState ⟨d,G,p.filling.leftPosition (.search,p.point)⟩) := by
    simpa only [lp] using root
  have eq := NullaryExecution.pointed_class_exact_equiv_of_left_rooted
    ContractionIdempotence.template_noInputs ContractionIdempotence.template_paddingClosed
    p.filling closed (p.idem_holeFree.mp closed) (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq) lr
  refine ⟨by simpa only [lp,rp] using eq,?_⟩
  change Search.RootedFrom H 0 (.search,w)
  simpa only [rp] using (p.filling.nullary_rooted_iff
    ContractionIdempotence.template_noInputs closed 0 (.search,p.point)).mp lr


theorem labels {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness T G v H w) : G.vertexLabel v = H.vertexLabel w := by
  have right := (BoundaryIso.ofDeepIso p.filling.rightIso).vertex_label
    (Net.Expansion.host p.filling.context p.filling.right p.point)
  change H.vertexLabel (p.filling.rightPosition (.search,p.point)).2 = _ at right
  rw [p.right] at right
  exact p.label.symm.trans (right.trans (Net.Expansion.host_label _ _ _)).symm

theorem idem_rooted_iff {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness ContractionIdempotence.template G v H w) (closed : HoleFree G) :
    StateClass.Rooted (StateClass.ofState ⟨d,G,(.search,v)⟩) ↔
      StateClass.Rooted (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  change Search.RootedFrom G 0 (.search,v) ↔ Search.RootedFrom H 0 (.search,w)
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  simpa only [lp,rp] using p.filling.nullary_rooted_iff
    ContractionIdempotence.template_noInputs closed 0 (.search,p.point)

theorem quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : PointedWitness T G v H w) (closedT : T.OutputClosed)
    (left : HoleFree G) (right : HoleFree H) (typed : G.vertexLabel v = .term) :
    (Specimens.system T Specimens.allContexts closedT).Quasi Eq Eq
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  have lp : p.filling.leftPosition (.search,p.point) = (.search,v) := Prod.ext rfl p.left
  have rp : p.filling.rightPosition (.search,p.point) = (.search,w) := Prod.ext rfl p.right
  simpa only [lp,rp] using p.filling.quasi closedT left right (.search,p.point)
    (p.label.trans typed) (by intro eq; cases eq)
end PointedWitness

/-- One actual BPullW residual followed by the two Idem corrections required
by the paper's unchanged canonical two-use distributor. Reflexive corrections
cover all cases which need fewer Idem steps. -/
structure Residual {d I O} (G : Hypernet d I O) (v : G.Vertex)
    (H : Hypernet d I O) (w : H.Vertex) where
  middle : Hypernet d I O
  point : middle.Vertex
  next : Hypernet d I O
  nextPoint : next.Vertex
  paired : PointedWitness template G v middle point
  first : PointedWitness ContractionIdempotence.template middle point next nextPoint
  second : PointedWitness ContractionIdempotence.template next nextPoint H w

namespace Residual
noncomputable def direct {d I O} {G H : Hypernet d I O} {v w}
    (p : PointedWitness template G v H w) : Residual G v H w :=
  ⟨H,w,H,w,p,PointedWitness.refl H p.filling.focusFree.2 w,
    PointedWitness.refl H p.filling.focusFree.2 w⟩

noncomputable def congr {d I O} {G H A B : Hypernet d I O} {v w}
    (p : Residual G v H w) (f : DeepIso G A) (g : DeepIso H B) :
    Residual A (Port.map f.vertices.toFun v) B (Port.map g.vertices.toFun w) := by
  refine ⟨p.middle,p.point,p.next,p.nextPoint,?_,p.first,?_⟩
  · have q := p.paired.congr f (DeepIso.refl _)
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q
  · have q := p.second.congr (DeepIso.refl _) g
    simpa only [DeepIso.refl,Net.RelIso.refl,Bijection.refl,Port.map_id_fun,id_eq] using q

/-- The literal copying overlap has exactly this certified three-link residual:
one duplicated BPullW filling, then two actual Idem fillings. -/
noncomputable def copying {d n k h} (tree : ContractionTree .term (n+1))
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) (s : ShareSort) (free : FocusFree B) :
    Residual (CopyRule.after tree (lambdaPayload (betaBody B s))) (.input ⟨0,by simp⟩)
      (extend (CopyRule.after tree (lambdaPayload B)) s) (.input ⟨0,by simp⟩) := by
  let payloadFree : FocusFree (lambdaPayload B) :=
    ((extend_allLabels _ _ s).mp (payloadWitness B s 0 free).focusFree.2).1
  refine ⟨CopyRule.after tree (extend (lambdaPayload B) s),.input ⟨0,by simp⟩,
    CopyRow.intermediate tree (lambdaPayload B) s,.input ⟨0,by simp⟩,
    PointedWitness.input (copy_intermediateWitness tree B s free) _,
    PointedWitness.input (CopyRow.first tree (lambdaPayload B) s payloadFree) _,
    PointedWitness.input (CopyRow.finalSecond tree (lambdaPayload B) s payloadFree) _⟩


/-- The actual BPullW residual supplies an original quasi-specimen, with its
two completed Idem steps used only as exact semantic corrections afterward. -/
theorem quasi {d} {G H : Hypernet d [.term] []} {v w}
    (p : Residual G v H w) (left : HoleFree G)
    (typed : G.vertexLabel v = .term) (P U : CostOrder) :
    (Specimens.system template Specimens.allContexts template_outputClosed).Quasi
      (StateClass.machine.Refines P) (StateClass.machine.Refines U)
      (StateClass.ofState ⟨d,G,(.search,v)⟩) (StateClass.ofState ⟨d,H,(.search,w)⟩) := by
  intro lroot rroot
  have midClosed : HoleFree p.middle :=
    (p.paired.filling.allLabels_iff (T := template) _ (fun pair => pair.allLabels _)).mp left
  have nextClosed : HoleFree p.next := p.first.idem_holeFree.mp midClosed
  have nextRoot := (p.second.idem_rooted_iff nextClosed).mpr rroot
  have midRoot := (p.first.idem_rooted_iff midClosed).mpr nextRoot
  have midTyped := p.paired.labels.symm.trans typed
  have nextTyped := p.first.labels.symm.trans midTyped
  have one := p.first.idem_exact midClosed midTyped midRoot
  have two := p.second.idem_exact nextClosed nextTyped nextRoot
  obtain ⟨S,mode,sl,sr,l,r⟩ :=
    p.paired.quasi template_outputClosed left midClosed typed lroot midRoot
  refine ⟨S,mode,sl,sr,?_,?_⟩
  · rw [l]; exact Machine.Refines.refl P _
  · rw [r]
    exact (one.1.1.trans two.1.1).mono (fun {n m} eq => by cases eq; exact U.refl n)
end Residual
end Hypernets.Copying.BoxPullWeakening

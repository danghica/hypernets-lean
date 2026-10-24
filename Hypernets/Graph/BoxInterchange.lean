import Hypernets.Graph.DeepAssociativity
import Hypernets.Graph.PlugInterchange

/-! Local interchange of box-body changes with other edge replacements. -/
namespace Hypernets.Linear
open Graph
variable {Op : Type} {ops : Operations Op}

theorem replaceBox_other_label {d I O} (C : Hypernet ops (d+1) I O)
    (f : C.Edge) (b : Box (alphabet ops d)) (label : C.edgeLabel f = .inr b)
    (B : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term))
    (e : C.Edge) (ne : e ≠ f) :
    (replaceBox C f b label B).edgeLabel e = C.edgeLabel e := by
  simp [alphabet,nextAlphabet,ne]

/-- A shallow site outside a changed box keeps its ordered interface. -/
noncomputable def Site.afterBox {d I O} (C : Hypernet ops (d+1) I O)
    (e f : C.Edge) (ne : e ≠ f) (b : Box (alphabet ops d))
    (label : C.edgeLabel f = .inr b)
    (B : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term)) :
    Site ops (replaceBox C f b label B) (d+1)
      ((alphabet ops (d+1)).signature.input (C.edgeLabel e))
      ((alphabet ops (d+1)).signature.output (C.edgeLabel e)) :=
  (Site.shallow (replaceBox C f b label B) e).reinterface
    (congrArg _ (replaceBox_other_label C f b label B e ne))
    (congrArg _ (replaceBox_other_label C f b label B e ne))

/-- Ignore labels temporarily to reuse the ordered-incidence transport lemma. -/
noncomputable def replaceBox_incidence {d I O} (C : Hypernet ops (d+1) I O)
    (f : C.Edge) (b : Box (alphabet ops d)) (label : C.edgeLabel f = .inr b)
    (B : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term)) :
    Net.RelIso (fun _ _ => True) C (replaceBox C f b label B) where
  vertices := Bijection.refl _
  edges := Bijection.refl _
  internal_label _ := rfl
  edge_label _ := trivial
  source _ := by simp [Bijection.refl,replaceBox,Net.relabelEdges]
  target _ := by simp [Bijection.refl,replaceBox,Net.relabelEdges]

/-- Replacing a retained box body commutes with replacing a distinct shallow edge. -/
noncomputable def plug_retained_box_iso {d I O} (C : Hypernet ops (d+1) I O)
    (e f : C.Edge) (ne : f ≠ e) (b : Box (alphabet ops d))
    (label : C.edgeLabel f = .inr b)
    (H : Hypernet ops (d+1) ((alphabet ops (d+1)).signature.input (C.edgeLabel e))
      ((alphabet ops (d+1)).signature.output (C.edgeLabel e)))
    (B : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term)) :
    Net.Iso (replaceBox (C.plug e H) (.inl ⟨f,ne⟩) b label B)
      (plugAt (Site.afterBox C e f (Ne.symm ne) b label B) H) := by
  classical
  rw [Site.afterBox,plugAt_reinterface]
  let g := replaceBox_incidence C f b label B
  let hi := (congrArg (alphabet ops (d+1)).signature.input
    (replaceBox_other_label C f b label B e (Ne.symm ne))).symm
  let ho := (congrArg (alphabet ops (d+1)).signature.output
    (replaceBox_other_label C f b label B e (Ne.symm ne))).symm
  let p := g.plugHost e hi ho (fun _ => trivial) H
  refine {
    vertices := p.vertices
    edges := p.edges
    internal_label := p.internal_label
    source := p.source
    target := p.target
    edge_label := ?_ }
  intro x
  cases x with
  | inl x =>
      simp [plugAt,p,g,replaceBox_incidence,Net.RelIso.plugHost,Net.HostPlug.edges,
        Bijection.sum,Subtype.ext_iff,Bijection.except,Bijection.refl,replaceBox,Net.relabelEdges,
        Net.plug,Net.Replacement.edgeLabel,alphabet,nextAlphabet]
  | inr x =>
      simp [plugAt,p,g,replaceBox_incidence,Net.RelIso.plugHost,Net.HostPlug.edges,
        Bijection.sum,Bijection.refl,replaceBox,Net.relabelEdges,
        Net.plug,Net.Replacement.edgeLabel,Net.reboundary,alphabet,nextAlphabet]

/-- Changes in two distinct box bodies commute as graph records. -/
theorem replaceBox_comm {d I O} (C : Hypernet ops (d+1) I O)
    (e f : C.Edge) (ne : f ≠ e) (b c : Box (alphabet ops d))
    (le : C.edgeLabel e = .inr b) (lf : C.edgeLabel f = .inr c)
    (A : Hypernet ops d [.term] (List.replicate (b.bound+b.free) .term))
    (B : Hypernet ops d [.term] (List.replicate (c.bound+c.free) .term)) :
    replaceBox (replaceBox C e b le A) f c
      ((replaceBox_other_label C e b le A f ne).trans lf) B =
    replaceBox (replaceBox C f c lf B) e b
      ((replaceBox_other_label C f c lf B e (Ne.symm ne)).trans le) A := by
  classical
  simp only [replaceBox,Net.relabelEdges]
  congr 1
  funext x
  by_cases he : x = e
  · subst x; simp [alphabet,nextAlphabet,Ne.symm ne]
  · by_cases hf : x = f
    · subst x; simp [alphabet,nextAlphabet,ne]
    · simp [alphabet,nextAlphabet,he,hf]

end Hypernets.Linear

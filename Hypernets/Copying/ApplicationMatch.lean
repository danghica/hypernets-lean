import Hypernets.Copying.OpeningPresentation

/-! Intrinsic source data for beta: the application, lambda, box and ordered wiring.
The body's relation to the literal box label is recursive isomorphism. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.Application
open Graph MatchEmbedding

structure Match {d I O k h} (G : Hypernet (d+1) I O) (v : G.Vertex)
    (B : Hypernet d [.term] (environmentInterface (k+1) h)) where
  app : G.Edge
  lam : G.Edge
  boxEdge : G.Edge
  functionWire : G.Internal
  thunkWire : G.Internal
  argumentPort : G.Vertex
  head_at : HeadAt G v app (.operation .app)
  app_target : G.target app = [.internal functionWire,argumentPort]
  lambda_label : G.edgeLabel lam = primitiveLabel (d+1) (.operation .lam)
  lambda_source : G.source lam = [.internal functionWire]
  lambda_target : G.target lam = [.internal thunkWire]
  box_label : LabelEquiv (d+1) (G.edgeLabel boxEdge) (.inr ⟨1,k,h,Translation.castInterfaces rfl (by rw [Nat.add_comm k 1]) B⟩)
  box_source : G.source boxEdge = [.internal thunkWire]

namespace Match
variable {d I O k h} {G : Hypernet (d+1) I O} {v : G.Vertex}
    {B : Hypernet d [.term] (environmentInterface (k+1) h)}

/-- All source occurrences and attachment ports are uniquely determined before opening. -/
theorem shape_unique {l j} {C : Hypernet d [.term] (environmentInterface (l+1) j)}
    (a : Match G v B) (b : Match G v C) :
    a.app = b.app ∧ a.lam = b.lam ∧ a.boxEdge = b.boxEdge ∧
      a.functionWire = b.functionWire ∧ a.thunkWire = b.thunkWire ∧ a.argumentPort = b.argumentPort := by
  have app := (head_unique a.head_at b.head_at).1
  have targets := a.app_target.symm.trans ((congrArg G.target app).trans b.app_target)
  have funEq := Port.internal.inj (List.cons.inj targets).1
  have arg := (List.cons.inj (List.cons.inj targets).2).1
  have lam := G.source_unique (e := a.lam) (f := b.lam)
    (by rw [a.lambda_source]; exact List.mem_cons_self)
    (by rw [b.lambda_source,← funEq]; exact List.mem_cons_self)
  have thunk := Port.internal.inj (List.cons.inj
    (a.lambda_target.symm.trans ((congrArg G.target lam).trans b.lambda_target))).1
  have boxEq := G.source_unique (e := a.boxEdge) (f := b.boxEdge)
    (by rw [a.box_source]; exact List.mem_cons_self)
    (by rw [b.box_source,← thunk]; exact List.mem_cons_self)
  exact ⟨app,lam,boxEq,funEq,thunk,arg⟩

/-- The actual box label fixes all binder metadata and the complete recursive body class. -/
theorem bodies_related {l j} {C : Hypernet d [.term] (environmentInterface (l+1) j)}
    (a : Match G v B) (b : Match G v C) :
    BoxRelated (alphabet d) (fun B C => Nonempty (DeepIso B C)) ⟨1,k,h,Translation.castInterfaces rfl (by rw [Nat.add_comm k 1]) B⟩
      ⟨1,l,j,Translation.castInterfaces rfl (by rw [Nat.add_comm l 1]) C⟩ := by
  have eq := (shape_unique a b).2.2.1
  have right := b.box_label
  rw [← eq] at right
  exact labelEquiv_trans (d+1) (labelEquiv_symm (d+1) a.box_label) right

theorem output_length (a : Match G v B) :
    (a.argumentPort :: G.target a.boxEdge).length = (.term :: environmentInterface k h).length := by
  have len := G.target_length a.boxEdge
  have sig := labelEquiv_output (d+1) a.box_label
  rw [sig] at len
  change (G.target a.boxEdge).length = (environmentInterface k h).length at len
  simp only [List.length_cons,len]

/-- Embed body ports in the common source/body occurrence space. -/
def bodyPort (a : Match G v B) : (openBody B).Vertex → Port (G.Internal ⊕ (openBody B).Internal) I.length O.length
  | .internal x => .internal (.inr x)
  | .input _ => Port.map Sum.inl v
  | .output i => Port.map Sum.inl ((a.argumentPort :: G.target a.boxEdge)[i.val]'(by rw [a.output_length]; exact i.isLt))

/-- Delete the app/lambda/box frame, retain the host, and expose the complete padded body. -/
@[reducible] def presentation (a : Match G v B) : Opening.Presentation (d+1) I O where
  Vertex := G.Internal ⊕ (openBody B).Internal
  Edge := G.Edge ⊕ (openBody B).Edge
  vertexLabel := Sum.elim G.internalLabel (openBody B).internalLabel
  edgeLabel := Sum.elim G.edgeLabel (openBody B).edgeLabel
  keepVertex
    | .inl x => x ≠ a.functionWire ∧ x ≠ a.thunkWire
    | .inr _ => True
  keepEdge
    | .inl e => e ≠ a.app ∧ e ≠ a.lam ∧ e ≠ a.boxEdge
    | .inr _ => True
  source
    | .inl e => (G.source e).map (Port.map Sum.inl)
    | .inr e => ((openBody B).source e).map a.bodyPort
  target
    | .inl e => (G.target e).map (Port.map Sum.inl)
    | .inr e => ((openBody B).target e).map a.bodyPort
end Match
end Hypernets.Copying.Application

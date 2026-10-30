import Hypernets.Copying.ContractionTreeGraft
import Hypernets.Copying.SharingTreeAlgebra

/-! Genuine filling certificates through the literal graft context. Residual
weakening and grafting need only the already proved exact sharing relation;
no unproved associativity of copying or transitivity of its template is used. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying.ContractionTree.Graft
open Graph Opening

/-- Simultaneous recursive certificates lift through the actual two-hole
partial serial context, retaining its selected port and all remaining inputs. -/
noncomputable def witness {T : PreTemplate} {d a b O} {s : ShareSort}
    {P Q : Hypernet d (List.replicate a s.wire) [s.wire]}
    {G H : Hypernet d (List.replicate (b+1) s.wire) O}
    (p : FillingWitness T P Q) (q : FillingWitness T G H) (j : Fin (b+1)) :
    FillingWitness T (net P G j) (net Q H j) := by
  apply FillingWitness.expand
  intro e
  cases d <;> cases e
  all_goals first | exact p | exact q

/-- Actual primitive-tree arity transport changes only the equal external
index type. It neither permutes ports nor changes either original tree. -/
def recount {s a b} (same : a = b) (P : ContractionTree s a) : ContractionTree s b :=
  same ▸ P

def recount_iso {s a b} (same : a = b) (P : ContractionTree s a) (d : Nat) :
    DeepIso ((recount same P).atDepth d)
      ((P.atDepth d).reboundary (congrArg (fun n => List.replicate n s.wire) same) rfl) := by
  cases same
  simpa only [recount,Net.reboundary_refl] using DeepIso.refl (P.atDepth d)

/-- Name the original full graft with the successor arity required by the
unchanged original copying rule. The first input remains upstream input zero. -/
def copyTree {m b} (P : ContractionTree .term (m+1))
    (T : ContractionTree .term (b+1)) (j : Fin (b+1)) : ContractionTree .term (m+b+1) :=
  recount (by omega) (P.graftInput T j)

/-- The original raised copying tree has exactly the literal two-component
graft, up to its explicit equal-interface cast and representation isomorphism. -/
def copyTree_iso {m b} (P : ContractionTree .term (m+1))
    (T : ContractionTree .term (b+1)) (j : Fin (b+1)) (d : Nat) :
    DeepIso ((copyTree P T j).atDepth d)
      ((net (P.atDepth d) (T.atDepth d) j).reboundary (by congr 1; omega) rfl) := by
  exact (recount_iso (by omega) (P.graftInput T j) d).trans
    (CopyRule.reboundaryIso (graftInput_iso P T j d) (by congr 1; omega) rfl)

/-- Closing the active upstream input before or after the graft gives actual
same-interface contraction trees. Their relation is the independently proved
sharing algebra, not an asserted graph isomorphism or a copying axiom. -/
noncomputable def residual_graft_witness {m b} (P : ContractionTree .term (m+1))
    (T : ContractionTree .term (b+1)) (j : Fin (b+1)) (d : Nat) :
    FillingWitness SharingTreeAlgebra.template
      ((CopyRule.residualTree (copyTree P T j)).atDepth d)
      (((CopyRule.residualTree P).graftInput T j).atDepth d) :=
  FillingWitness.of_rel 0 (SharingTreeAlgebra.literal
    (CopyRule.residualTree (copyTree P T j)) ((CopyRule.residualTree P).graftInput T j) d)

/-- The same residual certificate targets the literal generic graft graph,
so it can be used directly inside the three-payload copying diagram. -/
noncomputable def residual_graft_net_witness {m b} (P : ContractionTree .term (m+1))
    (T : ContractionTree .term (b+1)) (j : Fin (b+1)) (d : Nat) :
    FillingWitness SharingTreeAlgebra.template
      (CopyRule.residual (copyTree P T j) d)
      (net (CopyRule.residual P d) (T.atDepth d) j) :=
  (residual_graft_witness P T j d).congr (DeepIso.refl _)
    (graftInput_iso (CopyRule.residualTree P) T j d)

end Hypernets.Copying.ContractionTree.Graft

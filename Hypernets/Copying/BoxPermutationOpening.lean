import Hypernets.Copying.PermutationAssembly

/-! The BPerm / micro-beta overlap: bound wires are fixed, free wires compensated,
and both sides perform the original machine's one compute (or six opening) steps. -/
set_option backward.isDefEq.respectTransparency false
namespace Hypernets.Copying
open Graph
namespace TypedPermutation

theorem cast_trans {I J K : List Wire} (a : I = J) (b : J = K) (p : TypedPermutation I) :
    cast b (cast a p) = cast (a.trans b) p := by cases a; cases b; rfl
end TypedPermutation

namespace BoxPermutation.Opening
variable {d k h : Nat} {O : List Wire}

theorem interface (k h : Nat) : environmentInterface (k+1) h = .term :: environmentInterface k h := by
  simp [environmentInterface,List.replicate_succ]

/-- The raw translated body's action; output zero is the bound variable. -/
def bodyPermutation (p : TypedPermutation (environmentInterface k h)) :
    TypedPermutation (environmentInterface (k+1) h) :=
  TypedPermutation.cast (interface k h).symm (p.extend 1)

variable {B C : Hypernet d [.term] (environmentInterface (k+1) h)}
    (f : BoundaryIso B C) (p : TypedPermutation (environmentInterface k h))

/-- The exact action required by the one-bound-wire instance of Figure 21. -/
def Action : Prop := ∀ i, f.outputs.toFun i = (bodyPermutation p).bijection.toFun i

def openIso : BoundaryIso (Application.openBody B) (Application.openBody C) :=
  BoundaryIso.castInterfaces rfl (interface k h) rfl (interface k h) f.raise

theorem open_action (action : Action f p) : Application.SpliceBoundary.Action (openIso f) p := by
  have raised : ∀ i, f.raise.outputs.toFun i = (bodyPermutation p).bijection.toFun i := by
    intro i
    have eq := f.raise_output i
    rw [BoundaryIso.map_output] at eq
    exact (Port.output.inj eq).trans (action i)
  have cast := f.raise.cast_output_action (bodyPermutation p) (interface k h) raised
  simpa only [bodyPermutation,TypedPermutation.cast_trans,TypedPermutation.cast,
    Application.SpliceBoundary.Action,openIso] using cast

/-- The hypothesis is a genuine BPerm pair on the original lambda boxes. -/
theorem lambda_pair (action : Action f p) :
    BoxPermutation.UpToIso (Translation.lambdaBox B)
      (InterfacePermutation.net (Translation.lambdaBox C) p.symm) := by
  apply BoxPermutation.of_bodyIso (BoxPermutation.pair 1 p)
    (BoundaryIso.castInterfaces rfl _ rfl _ f)
  have cast := f.cast_output_action (bodyPermutation p)
    (congrArg (fun n => environmentInterface n h) (Nat.add_comm k 1)) action
  simpa only [bodyPermutation,TypedPermutation.cast_trans,BoxPermutation.pair,BoxPermutation.inner] using cast

/-- Lift the genuine box pair to the literal application redex and move its
compensation through serial and tensor assembly. This is a structural derivation,
which identifies the two sources of the operational diamond below. -/
theorem source_pair (G : Hypernet (d+1) [.term] O) (action : Action f p) :
    BoxPermutation.Derivation (Application.before B G)
      (InterfacePermutation.net (Application.before C G) (p.append (.refl O)).symm) := by
  have boxes := BoxPermutation.Derivation.of_upToIso (lambda_pair f p action)
  have closures := ((BoxPermutation.Derivation.refl (primitiveNet (d+1) (.operation .lam))).serial boxes).trans
    (.iso (InterfacePermutation.serial _ (Translation.lambdaBox C) p.symm))
  have operands := (closures.tensor (.refl G)).trans
    (.iso (InterfacePermutation.tensor_left (Application.closure C) G p.symm))
  have applications := ((BoxPermutation.Derivation.refl (primitiveNet (d+1) (.operation .app))).serial operands).trans
    (.iso (InterfacePermutation.serial _ (Net.Tensor.net (Application.closure C) G)
      (p.symm.append (.refl O))))
  simpa only [Application.before,Application.closure,TypedPermutation.append_symm,TypedPermutation.symm_refl] using applications

/-- Opening the two bodies transports the free interface and leaves the whole argument fixed. -/
def afterIso (G : Hypernet (d+1) [.term] O) (action : Action f p) :
    BoundaryIso (Application.after B G) (Application.after C G) :=
  Application.SpliceBoundary.iso (openIso f) p G (open_action f p action)

/-- After inverse compensation the successors are recursively isomorphic with
pointwise fixed external boundaries. No BPerm step remains inside them. -/
def afterCompensated (G : Hypernet (d+1) [.term] O) (action : Action f p) :
    DeepIso (Application.after B G)
      (InterfacePermutation.net (Application.after C G) (p.append (.refl O)).symm) :=
  Application.SpliceBoundary.compensate (openIso f) p G (open_action f p action)

/-- The body-side edge map never substitutes, deletes or duplicates an argument edge. -/
theorem argument_edge (G : Hypernet (d+1) [.term] O) (action : Action f p) (e : G.Edge) :
    (afterCompensated f p G action).edges.toFun (Application.argumentEdge B G e) =
      Application.argumentEdge C G e := rfl

/-- The local robustness diamond is an actual one-step computation on each side.
The compensating output permutation is implemented by context closure. -/
theorem beta_diamond (G : Hypernet (d+1) [.term] O) (stable : Stable G) (action : Action f p) :
    Combined.Step ⟨Application.before B G,(.rewrite,.input 0)⟩
      ⟨Application.after B G,(.search,.input 0)⟩ ∧
    Combined.Step (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before C G,(.rewrite,.input 0)⟩)
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.after C G,(.search,.input 0)⟩) ∧
    Nonempty (DeepIso (Application.after B G)
      (InterfacePermutation.net (Application.after C G) (p.append (.refl O)).symm)) :=
  ⟨Combined.local_step (.beta B G stable),
    InterfacePermutation.step _ (Combined.local_step (.beta C G stable)),
    ⟨afterCompensated f p G action⟩⟩

/-- Including search, both sides use exactly six transitions. Bodies and callbacks
are arbitrary; termination of the exposed body is deliberately not a premise. -/
theorem opening_diamond (G : Hypernet (d+1) [.term] O) (stable : Stable G) (action : Action f p) :
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      ⟨Application.before B G,(.search,.input 0)⟩
      ⟨Application.after B G,(.search,.input 0)⟩ ∧
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before C G,(.search,.input 0)⟩)
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.after C G,(.search,.input 0)⟩) ∧
    Nonempty (DeepIso (Application.after B G)
      (InterfacePermutation.net (Application.after C G) (p.append (.refl O)).symm)) :=
  ⟨Combined.application_run (Application.opening_run B G stable),
    InterfacePermutation.run _ (Combined.application_run (Application.opening_run C G stable)),
    ⟨afterCompensated f p G action⟩⟩
/-- Literal free permutation of an arbitrary original body satisfies the
required action by construction; it is not an extra semantic assumption. -/
theorem permuted_action (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (p : TypedPermutation (environmentInterface k h)) :
    Action (InterfacePermutation.iso B (bodyPermutation p)) p := fun _ => rfl

/-- At every finite allowance and every free variable/atom interface, the actual
permuted-body application has the proved six-step matching diagram. -/
theorem permuted_opening (B : Hypernet d [.term] (environmentInterface (k+1) h))
    (G : Hypernet (d+1) [.term] O) (stable : Stable G)
    (p : TypedPermutation (environmentInterface k h)) :
    BoxPermutation.Derivation (Application.before B G)
      (InterfacePermutation.net
        (Application.before (InterfacePermutation.net B (bodyPermutation p)) G)
        (p.append (.refl O)).symm) ∧
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      ⟨Application.before B G,(.search,.input 0)⟩
      ⟨Application.after B G,(.search,.input 0)⟩ ∧
    (Combined.machine (d+1) [.term] (environmentInterface k h ++ O)).Steps 6
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.before (InterfacePermutation.net B (bodyPermutation p)) G,(.search,.input 0)⟩)
      (InterfacePermutation.state (p.append (.refl O)).symm
        ⟨Application.after (InterfacePermutation.net B (bodyPermutation p)) G,(.search,.input 0)⟩) ∧
    Nonempty (DeepIso (Application.after B G)
      (InterfacePermutation.net
        (Application.after (InterfacePermutation.net B (bodyPermutation p)) G)
        (p.append (.refl O)).symm)) :=
  ⟨source_pair _ p G (permuted_action B p),
    opening_diamond _ p G stable (permuted_action B p)⟩

/-- Once opened, the two successors have identical exact successful cost spectra. -/
theorem successor_costs (G : Hypernet (d+1) [.term] O) (action : Action f p) (n : Nat) :
    Combined.TerminatesIn n ⟨Application.after B G,(.search,.input 0)⟩ ↔
    Combined.TerminatesIn n (InterfacePermutation.state (p.append (.refl O)).symm
      ⟨Application.after C G,(.search,.input 0)⟩) :=
  Combined.terminatesIn_iso
    (s := ⟨Application.after B G,(.search,.input 0)⟩)
    (t := InterfacePermutation.state (p.append (.refl O)).symm
      ⟨Application.after C G,(.search,.input 0)⟩)
    { graph := afterCompensated f p G action, mode := rfl, vertex := rfl } n
end BoxPermutation.Opening
end Hypernets.Copying

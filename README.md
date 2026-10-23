# Hypernets in Lean 4

A formalization in progress of Dan R. Ghica, Koko Muroya, and Todd Waugh
Ambridge, **A robust graph-based approach to observational equivalence**.
The reference version is [arXiv:1907.01257v5](https://arxiv.org/abs/1907.01257v5),
23 April 2025, published in LMCS 21(2:8), 2025.

The target milestone is the general sufficiency-of-robustness theorem
(Theorem 6), including both its forward and converse clauses.

## Current status

**The concrete hypernet theorem is not yet formalized.** The checked development
contains its abstract transition-system argument and a conditional specimen
argument. There are no `sorry` proofs or project-specific axioms.

The principal completed result is `Machine.CountingSimulation.sound`, the
content of Proposition 37, generalized to arbitrary deterministic machines.
It includes the stuck-state alternative and all three quantitative relations.

Theorems `SpecimenSystem.contextual_sufficiency` and
`SpecimenSystem.contextual_sufficiency_converse` prove abstract counterparts of
both clauses of Theorem 6. They take a `SpecimenSystem` and an `initial_lift`
proof as arguments. The system's fields include substantive graph obligations:
rootedness preservation, final-state agreement, and context-only traversal.
These are explicit hypotheses, **not proofs that the paper's UAM satisfies
them**. No concrete hypernet, plugging operation, or UAM instance exists yet.

The abstract `InputSafe`, `Robust`, and `Quasi` definitions express the
consequences of the paper's conditions consumed by the proof. They restrict
attention to rooted specimens and, for quasi-specimens, non-rewrite focuses.
Their equivalence to the paper's concrete graph definitions remains to prove.
Output-closure and refocusing have not been independently defined: their
consequences are currently requirements of the specimen interface.

## Checked source

- `Hypernets/Transition.lean`: counted executions, deterministic prefix and
  terminal-uniqueness lemmas, stuck states, and removal of an initial step.
- `Hypernets/Quantitative.lean`: cost preorders, reasonable triples (§8.4),
  state refinement (§7.1), and refinement preorder/monotonicity lemmas.
- `Hypernets/Simulation.lean`: counting simulation up to two refinements,
  and its soundness proof (Proposition 37).
- `Hypernets/Contextual.lean`: type-indexed observations with partial
  initialization, and the logical contextual-lifting argument (Proposition 38).
- `Hypernets/LocalReasoning.lean`: abstract specimens, rooted lifting, all
  three input-safety cases, robustness, forward and converse simulation
  proofs, and conditional contextual sufficiency (Proposition 40/Theorem 6).
- `Hypernets/Examples.lean`: semantic regression proofs, including a crashing
  computation related to a looping one, quantitative refinement direction,
  and the converse proof's zero-right-step safety case.
- `Hypernets/Audit.lean`: reports the axioms of the main theorems.

The implementation uses Lean's bundled `Std`, with no external library
dependencies. The toolchain is pinned in `lean-toolchain`.

## Checking

With the pinned Lean toolchain available:

```sh
lake build
lake env lean Hypernets/Audit.lean
```

For this workspace, an official macOS ARM compiler is available locally under
the ignored `.toolchains/` directory. This command selects it if present,
then builds the library and runs the axiom audit:

```sh
bash scripts/check.sh
```

The audit must not report `sorryAx` or a project-specific axiom. Standard Lean
logical axioms, if used, are shown explicitly.

## Remaining work toward the milestone

1. Encode finite labelled monoidal hypergraphs with ordered interfaces and
   the paper's incidence conditions (§3). Define nesting and graph isomorphism.
2. Define interface-compatible contexts and plugging (§6.3, Appendix B), with
   renaming, associativity, and well-formedness lemmas. Keep concrete graph
   representatives until their operations are proved invariant under isomorphism.
3. Define focussed states, search and rewrite transitions, rootedness,
   determinism, and refocusing (§§5–7, Appendices C–D).
4. Define concrete type-indexed pre-templates, specimens, quasi-specimens,
   output-closure, input-safety, and robustness (§8).
5. Construct `SpecimenSystem` for those concrete definitions. Prove its
   locality fields (especially Lemma 39), `initial_lift`, and the bridges from
   concrete safety/robustness to the abstract predicates.
6. Instantiate the checked sufficiency results to obtain Theorem 6 with only
   the paper's stated hypotheses. At that point the milestone is complete.

The copying UAM, lambda-term translation, and example program equivalences
are later milestones; the small abstract examples currently included do not
formalize those parts of the paper.

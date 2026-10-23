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
argument, together with a concrete finite graph and boxed-hypernet foundation.
There are no `sorry` proofs or project-specific axioms.

The principal completed result is `Machine.CountingSimulation.sound`, the
content of Proposition 37, generalized to arbitrary deterministic machines.
It includes the stuck-state alternative and all three quantitative relations.

Theorems `SpecimenSystem.contextual_sufficiency` and
`SpecimenSystem.contextual_sufficiency_converse` prove abstract counterparts of
both clauses of Theorem 6. They take a `SpecimenSystem` and an `initial_lift`
proof as arguments. The system's fields include substantive graph obligations:
rootedness preservation, final-state agreement, and context-only traversal.
These are explicit hypotheses, **not proofs that the paper's UAM satisfies
them**. Concrete hypernets and plugging now exist; a concrete UAM and its
connection to this interface do not yet exist.

The abstract `InputSafe`, `Robust`, and `Quasi` definitions express the
consequences of the paper's conditions consumed by the proof. They restrict
attention to rooted specimens and, for quasi-specimens, non-rewrite focuses.
Their equivalence to the paper's concrete graph definitions remains to prove.
Output-closure and refocusing have not been independently defined: their
consequences are currently requirements of the specimen interface.

## Concrete graph milestone

The new `Hypernets/Graph/` development proves structural results about actual
finite graphs. Its well-formedness and locality properties are not supplied as
extra abstract assumptions:

- `Net` implements the four incidence conditions of §3.1, fixed operation
  signatures, and ordered input/output interfaces. Internal vertices and edges
  have explicit finite enumerations. Self-loops and graph cycles are permitted.
- `Net.plug` replaces a shallow edge by a graph of precisely its type and proves
  all graph invariants are preserved. The entire outer interface is unchanged.
  The implementation supports self-loop holes: the replacement map is proved
  injective separately on sources and targets, without assuming global injectivity.
- Surviving context paths are preserved and reflected by plugging. Inserted
  paths are preserved; they are reflected when the hole is non-self-looping,
  exactly the additional condition in Appendix B. A concrete self-loop
  counterexample proves that omitting that condition would be false.
- Vertex and edge renaming, graph isomorphism (identity, inverse, composition),
  and path invariance are proved. `Net.plugIso` proves that isomorphic
  replacements give isomorphic whole graphs in any shallow context.
- The linear UAM's wire types, operations, variables, focus labels, typed holes,
  and boxed hypernets are represented at every finite depth. A box binding `n`
  variables and exposing `m` has type `T^n(*) => *^m`, while its body has type
  `* => *^(n+m)`. Depth promotion preserves the outer incidence structure.
- A recursive enumeration proves finiteness of all shallow and deep edge
  occurrences (the content of Appendix A, Lemma 19, for this typed hierarchy).
  Occurrences in two distinct boxes have distinct addresses, even for equal bodies.
- Hole-label uniqueness is defined over all depths; `Context` is the corresponding
  subtype. Boxing is proved to preserve this context condition.
- `Linear.plugAt` performs type-correct replacement at any addressed box depth.
  Deep replacement preserves enclosing source/target lists and every other outer
  edge label. Examples fill a hole inside a box and prove the old hole is removed.
- Operation paths from inputs have unique edge sequences and starting inputs.
  Reverse traversal determinism is derived from graph incidence, and a positive
  operation cycle cannot occur on such a path. `Linear.operation_path_unique`
  specializes this to typed hypernets without an additional determinism premise
  (the graph-theoretic content of Lemma 22).

`Net.Iso` fixes edge labels and handles carrier renaming at one graph level.
The new `DeepIso` extends this to independently renamed box contents, as described
below. The context calculus proves preservation of unique hole labels under
explicit freshness conditions at arbitrary depth. Plugging associativity remains
to prove. The typed, depth-indexed hierarchy includes explicit binder
metadata on box labels; a formal representation theorem relating it to the
paper's set-based, graph-labelled presentation remains to prove. These
distinctions are part of the remaining work below.

## Context calculus milestone

The concrete context condition is now preserved by plugging, with its freshness
requirements proved explicitly rather than left as abstract locality laws:

- Occurrence fibres identify an address by its outer edge and a position in that
  edge's label. A proved bijection relates them to the existing deep occurrences
  and preserves hole lookup.
- Shallow plugging has an exact hole inventory: retained host holes together
  with replacement holes. Only occurrences below the removed edge are discarded.
- Given two contexts, the result is a context **if and only if** no retained host
  hole label occurs in the replacement. The consumed label can be reused.
- Concrete injective provenance is constructed through every enclosing box.
  It proves context closure at any addressed depth under retained-origin
  compatibility, with full host/replacement disjointness as a simpler sufficient
  condition. Hole-free replacements need no separate freshness proof.
- `Context.plugFresh` and `Context.plugAt` return certified contexts. Graph
  isomorphisms preserve hole inventories and the unique-hole context condition.
- Regressions prove valid reuse of a consumed label, global absence of holes
  after filling inside a box, and failure of uniqueness when two individually
  valid contexts introduce a retained/inserted label collision.

## Exact deep inventory milestone

The inventory and sharp freshness theorems now hold at every finite box depth:

- `SiteRetainedHole` computes retained host labels from the original graph and
  address alone. It does not depend on the replacement or a provenance certificate.
- `plugAt_hasHole_iff` proves that the result contains exactly the retained host
  labels and the replacement labels, without uniqueness or freshness assumptions.
- For a host context, `plugAt_uniqueHoles_iff` proves that the result has unique
  holes **if and only if** the replacement has unique holes and satisfies
  `SiteFresh`. Replacement uniqueness is itself a necessary conclusion.
- `Context.plugAtFresh` packages the resulting context using this exact condition.
  Full host/replacement disjointness is no longer required.
- `plugAt_holeFree_iff` characterizes complete removal of holes, and
  `plugAt_consumed_hole_iff` proves that a consumed label remains precisely when
  the replacement reintroduces it.
- Concrete boxed regressions verify consumed-label reuse, genuine removal, and
  failure of uniqueness when an inserted label collides with a surviving sibling.

## Recursive isomorphism milestone

`DeepIso` now compares complete finite hierarchies, allowing independent
vertex and edge renaming in each box body:

- `LabelEquiv` preserves primitive labels, binder metadata, ordered signatures,
  and the operation predicate. Identity, inverse, and composition are proved.
- Adjacency, paths, and complete operation traces are preserved and reflected.
- Concrete injective maps transport occurrences through every box. Recursive
  isomorphisms preserve hole inventories, hole-freeness, and context validity.
- `plugAt_deepIso` proves replacement congruence at every addressed depth, with
  no freshness, context-uniqueness, or non-self-loop premise.
- `HypernetModuloIso` quotients graphs at each fixed depth and interface by this
  equivalence. `plugAtModuloIso` is well-defined on replacement classes for a
  fixed concrete host and site; context validity also descends to the quotient.
- A checked example renames the two edges inside a box. The boxes are recursively
  isomorphic but admit no literal-label `Net.Iso`, demonstrating the strict extension.

## Site transport milestone

- `Site.transport_exists` proves that every addressed occurrence has a structurally
  corresponding site in a recursively isomorphic host, at the same depth and interface.
- `SiteIso.plug_congr` proves congruence when both host and replacement are renamed.
  No freshness or non-self-loop assumption is needed for congruence.
- Retained hole inventories, exact freshness, and result context validity are invariant.
  Quotient substitution agrees before and after host/site transport.
- A boxed edge-swap regression checks the moved address. A counterexample proves that
  keeping the former numerical address can give a non-isomorphic substitution result.

Transport chooses inner isomorphisms classically; no canonical choice or round-trip
law is asserted. The host/site pair is not yet quotiented. Plugging associativity,
comparison across different depth bounds, and representation adequacy remain open. The concrete UAM and its
bridge to Theorem 6 remain the main later work.

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
- `Hypernets/Graph/Finite.lean`, `Basic.lean`, and `Constructors.lean`: finite
  carriers, concrete typed hypergraphs, empty graphs, and single-operation graphs.
- `Hypernets/Graph/Plugging.lean` and `Paths.lean`: well-formed shallow plugging
  and the path preservation/reflection theorems of Appendix B.
- `Hypernets/Graph/Isomorphism.lean` and `PlugIsomorphism.lean`: renaming,
  isomorphism, path invariance, and congruence of shallow plugging.
- `Hypernets/Graph/Hierarchy.lean`: typed finite-depth hypernets and contexts,
  depth promotion, finite deep occurrences, and concrete operation-path uniqueness.
- `Hypernets/Graph/OperationPaths.lean`: reverse traversal, exact path uniqueness,
  and exclusion of operation cycles on input-rooted paths.
- `Hypernets/Graph/DeepPlugging.lean`: addressed replacement at arbitrary depth
  and its enclosing-graph locality properties.
- `Hypernets/Graph/Examples.lean` and `Audit.lean`: graph-level regression proofs
  and explicit logical-dependency reports for the concrete constructions.
- `Hypernets/Graph/Occurrences.lean`: label-local occurrence fibres, their
  bijection with deep addresses, observation preservation, and edge-map transport.
- `Hypernets/Graph/ContextPlugging.lean`: hole inventories, isomorphism invariance,
  provenance, exact shallow inventory, sharp freshness, and certified context plugging.
- `Hypernets/Graph/DeepContext.lean`: provenance through box replacement and
  certified context closure for replacement at any addressed depth.
- `Hypernets/Graph/DeepInventory.lean`: exact deep inventories, box decomposition,
  necessary-and-sufficient context closure, hole-freeness, and selected-label consumption.
- `Hypernets/Graph/DeepInventoryExamples.lean`: deep reuse, removal and collision regressions.
- `Hypernets/Graph/ContextExamples.lean`: hole-free filling, consumed-label reuse,
  and an explicit collision between two individually valid contexts.

- `Hypernets/Graph/RelIso.lean` and `RelIsoPlug.lean`: incidence isomorphisms
  relative to a label relation and generic shallow replacement congruence.
- `Hypernets/Graph/RecursiveIso.lean`: recursive label equivalence, deep
  isomorphisms, equivalence laws, signatures, and operation-path invariance.
- `Hypernets/Graph/RecursiveIsoHoles.lean`: occurrence embeddings and invariance
  of hole inventories, hole-freeness, and contexts under recursive renaming.
- `Hypernets/Graph/RecursiveIsoPlug.lean`: deep congruence, exact freshness
  invariance, recursive isomorphism classes, and quotient replacement.
- `Hypernets/Graph/RecursiveIsoExamples.lean`: body renaming, the strict extension
  beyond literal-label isomorphism, and concrete quotient/congruence regressions.
- `Hypernets/Graph/TransportPlug.lean`: boundary transport, complement bijections,
  ordered attachment transport, and generic shallow host congruence.
- `Hypernets/Graph/SiteTransport.lean`: structural site correspondence, existence
  of transport, simultaneous congruence, quotient invariance, and exact freshness.
- `Hypernets/Graph/SiteTransportExamples.lean`: moved-address and wrong-address regressions.

The implementation uses Lean's bundled `Std`, with no external library
dependencies. The toolchain is pinned in `lean-toolchain`.

## Mathematical commentary

The [mathematical commentary](docs/mathematical-commentary/main.tex) explains
all 477 definitions and proved statements in the abstract and concrete graph
development, including regression examples, in mathematical English. Its 483
source-fragment links point to immutable code revision `693a25d`. It distinguishes
proved graph properties, conditional specimen results, and the remaining
obligations for the paper's concrete theorem. Appendix A is an alphabetical
glossary of 126 technical terms, with short descriptions and internal PDF links
to the definitions. The source checker also validates its definition destinations.

Read the [compiled PDF](output/pdf/hypernets-mathematical-commentary.pdf), or open
the LaTeX project folder in the Codex editor. To reproduce both the source-link
check and PDF from that folder, run `make` with Python 3 and `latexmk` available.
The PDF is exported to `output/pdf/` at the repository root. To check links alone:

```sh
python3 docs/mathematical-commentary/check_sources.py
```

## Checking

With the pinned Lean toolchain available:

```sh
lake build
lake env lean Hypernets/Audit.lean
lake env lean Hypernets/Graph/Audit.lean
```

For this workspace, an official macOS ARM compiler is available locally under
the ignored `.toolchains/` directory. This command selects it if present,
then builds the library and runs both axiom audits:

```sh
bash scripts/check.sh
```

The audit must not report `sorryAx` or a project-specific axiom. Standard Lean
logical axioms, if used, are shown explicitly.

## Remaining work toward the milestone

1. Prove adequacy of the typed graph representation, relate different depth
   bounds, quotient host/site pairs, and prove the context
   algebra, especially associativity of plugging. Recursive box isomorphism
   and simultaneous host/replacement congruence through transported sites are now
   proved. Global hole-label uniqueness under freshness, exact hole inventories, and sharp context closure are now
   checked even for deep replacement.
2. Define focussed states, search and rewrite transitions, rootedness,
   determinism, and refocusing (§§5–7, Appendices C–D).
3. Define concrete type-indexed pre-templates, specimens, quasi-specimens,
   output-closure, input-safety, and robustness (§8).
4. Construct `SpecimenSystem` for those concrete definitions. Prove its
   locality fields (especially Lemma 39), `initial_lift`, and the bridges from
   concrete safety/robustness to the abstract predicates.
5. Instantiate the checked sufficiency results to obtain Theorem 6 with only
   the paper's stated hypotheses. At that point the milestone is complete.

The copying UAM, lambda-term translation, and example program equivalences
are later milestones; the current abstract and graph-level examples do not
formalize those parts of the paper.

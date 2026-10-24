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
Output-closure has not yet been defined concretely. Refocusing now has a concrete
state-class definition and a search preservation theorem; the abstract interface
still assumes the required locality consequences.

## Paper proof dependency map

- **Proposition 37 — checked:** `Machine.CountingSimulation.sound` follows the
  quantitative soundness proof for deterministic machines.
- **Proposition 40 — conditional:** `SpecimenSystem.countingSimulation` and its
  converse use explicit specimen locality, safety, and robustness assumptions.
- **Lemma 39(1), Appendix F.4 — boundary argument checked:**
  `Focussed.fillings_boundary_agreement` proves initial/final agreement for two
  finite sequences of focus-free fillings of a common focussed graph, including
  deep sites. It preserves the focus mode and input status of its source, just
  as the paper does. Connecting paper specimens to these filling sequences is
  still an adequacy obligation; both shallow and recursive deep specimens now
  have direct initial/final agreement for their actual filled states.
- **Lemma 39(2): checked for recursive specimens; (3): search core checked.**
  Joint rootedness and output closure prove non-exiting. Erasure commutation and
  the entering/exiting classification synchronize actual settled search steps
  to rooted endpoints at a remote coordinate. Successor-specimen packaging and
  the full-UAM context-step law remain open.
- **Contextual search adequacy: checked.** Finite two-edge interaction patterns
  plugged into explicit focus-free simple hole contexts coincide with
  erasure-based state search in both directions. Arbitrary simple contexts,
  output-boundary fragments, recursive endpoint renaming, and self-looping
  attachments are covered.
- **Proposition 38 — initial bridge open:** the logical lifting theorem is
  checked and initial focus attachment is constructed. Concrete observations and
  specimen witnesses must still discharge `initial_lift`.
- **Theorem 6 — still conditional:** the abstract pieces are combined, but a
  concrete `SpecimenSystem` and the safety/robustness bridges remain missing.
  Determinism and refocusing are hypotheses of the paper's theorem, not claims
  to prove for arbitrary extrinsic rewrite rules.

Contextual search adequacy and §6.4's concrete transition definitions are now
complete. The next dependencies are substitution rootedness, full-UAM structural
laws and the remaining specimen-interface laws.
The finite-depth typed representation and explicit isomorphisms are implementation
choices whose adequacy for the paper remains a separate obligation.

`Hypernets/Graph/Focused.lean` now defines global focus freedom, the unique
shallow non-exposed self-acyclic focus, and hole-free states of type `* → ε`.
It proves preservation through shallow/deep substitution and finite fillings.
`FocusedExamples.lean` checks a real focus-and-hole chain, distinguishes search
from finality, and rejects a focus hidden inside a box. These state-space and boundary results are now complemented by
`Search.lean`: the five Fig. 9 search rules on actual underlying graph coordinates,
with the active/passive operation partition, proved determinism, search boundary
laws, and preservation under shallow hole filling. `SearchExamples.lean` checks
argument order, skipping a thunk, nullary values, and variables. Coordinate
search has not yet been identified with rewriting explicit focussed states;
substitution and extrinsic computation are not yet defined.

`FocusInsertion.lean` now splits a term vertex to insert an actual focus edge,
proving all net invariants, global focus uniqueness, hole freedom, and contraction
of the new focus back to the original incidence lists. `SearchRealization.lean`
proves search preserves term typing, constructs genuine initial states, and gives
explicit focussed state endpoints for every typed coordinate search step.
`RealizationExamples.lean` checks initial/final value states and interior insertion.
`FocusErasure.lean` and `FocusRoundTrip.lean` now erase arbitrary closed focussed
graphs and prove that reinsertion recovers them by an explicit focus-preserving
isomorphism. `StateSearch.lean` extracts coordinates from arbitrary states and
defines actual-state search through erasure and reinsertion. It proves determinism
up to focussed isomorphism, target-renaming closure, and the initial/final search
boundary laws. `ErasureExamples.lean` proves an actual initial-value-to-final-state
search execution and tests recovery with an interior focus.

`InsertionRoundTrip.lean` now proves the opposite round trip, recovering both
underlying graph and insertion position. `SearchRenaming.lean` and
`InsertionRenaming.lean` transport the search rules and realized states through
isomorphisms. `RealizedSearch.lean` characterizes search from a realized state
exactly by coordinate search on its original graph, up to endpoint isomorphism.
`ErasureRenaming.lean` proves source invariance as well as invariance in both
arguments. `StateQuotient.lean` descends search and boundary observations to
literal-label state isomorphism classes and proves equality of successor classes.
`QuotientSearchExamples.lean` checks the specific initial-to-final value execution,
a reconstructed source, and uniqueness of its successor class.

`DeepFocus.lean`, `DeepSearchRenaming.lean`, `DeepInsertionRenaming.lean`, and
`DeepErasureRenaming.lean` extend focus and search transport to independent
renaming inside nested boxes. `DeepStateSearch.lean` and `DeepStateQuotient.lean`
construct recursively renamed state search and its deterministic quotient.
`StateQuotientBridge.lean` projects literal classes onto recursive classes and
lifts every recursive step from any specified literal source class.
`SearchQuotientExecutions.lean` proves exact-length execution lifting and
preservation/reflection of search termination. Its machine instances contain
search only; they are not the full UAM. `DeepSearchExamples.lean` checks recursive
box focus freedom and the exact-length execution bridge on the value example.

`StateRoots.lean` constructs canonical initial roots and concrete rootedness,
proving that search preserves both the underlying graph and rootedness.
`SearchReachability.lean` and `RootedPaths.lean` establish the operation-path
invariant and lift it through focus insertion. `RootedStatePaths.lean` proves
that a rooted state's actual focus source has an operation path from its
unique input (the concrete Lemma 23 conclusion). `RootedPathObstruction.lean`
proves the concrete Lemma 26(1) obstruction using the existing edge-path type.
`ConcreteRefocusing.lean` defines refocusing and proves it for search, leaving
the rewrite-preservation obligation explicit. `RootedExamples.lean` proves
the value execution rooted and the valid interior-focus state behind a variable
not rooted. These use the current erasure-based search semantics; contextual
local-rewrite adequacy is now proved in `HoleContextSearch.lean`.

The PDF's [Appendix B: remaining work](output/pdf/hypernets-mathematical-commentary.pdf#nameddest=appendix.B) contains four unfinished tasks. Search adequacy and the full UAM transition
definition are discharged; structural laws and the concrete robustness bridge remain open.

`OneWay.lean` defines the paper's term-to-term one-way predicate, proves its
invariance under recursive renaming and closure under one-way shallow filling,
and extracts operation paths from actual filled graphs. The resulting host
reachability reflection supports `OneWayObstruction.lean`: concrete Lemma 26(2)
now holds even for self-looping holes and host paths containing the hole.
The paired single-hole corollary is checked; the subsequent shallow
multi-hole milestone below supplies the next specimen-level result. `OneWayExamples.lean` includes a genuine
hole-containing context path whose one-way filling produces a non-rooted state,
and checks that operation paths to thunk outputs are permitted by one-wayness.

`Simultaneous.lean` now constructs actual simultaneous shallow expansion with
all finite graph invariants proved. `ExpansionPaths.lean` extracts local paths
and proves paired host-path reflection, allowing the one-way side to vary by
hole. `ShallowSpecimens.lean` defines concrete typed pre-templates,
output-closure, and shallow specimens, constructs their actual states, and
proves the shallow cases of Lemma 26(3) and Lemma 39(1), plus the jointly rooted
context-path consequence used by Lemma 39(2). The regressions include a genuine
two-hole focussed specimen and alternating one-way choices with no global
one-way side.

The sequential-realization milestone now connects every finite simultaneous
shallow family to an ordinary addressed-substitution run. ExpansionPeel.lean
constructs the one-step peeling isomorphism, and ExpansionCopies.lean restores
a host from arbitrary identity copies. ExpansionSequential.lean proves that
certified schedules constructed from finite covering lists yield the
simultaneous graph up to explicit isomorphism and are independent of order,
including in the recursive graph quotient. Their length is bounded by the
covering-list length. SequentialExamples.lean checks both alternating families
and schedules beginning at either of the two holes. These are graph
replacement results. The subsequent milestone below proves independent
interchange at arbitrary depth and constructs the host/site quotient.
DeepFillings.lean now defines recursive paired fillings through original box
bodies and proves global focus freedom. DeepSpecimens.lean constructs actual
deep-filled states and proves the Lemma 26(3) obstruction, the jointly rooted
context-path conclusion, and initial/final agreement. DeepSpecimenExamples.lean
constructs a closed specimen whose sole hole is inside a box, and proves that
the old shallow rules cannot close this same context. Finite original-hole tuple compatibility is now proved in TupleFillings.lean;
the full specimen interface remains open.

ExpansionSearch.lean now proves exact context search transport through recursive
fillings and reflection away from shallow hole boundaries. Entire executions
reflect in invariant regions; when all holes are strictly inside boxes, exact
successful coordinate-search costs are preserved and reflected. The same context
traces yield paired actual-state executions and rooted endpoints after focus
insertion. ExpansionSearchExamples.lean checks a rooted final state with a
deep-filled box and proves that unrestricted reflection fails at a shallow hole.
ExpansionErasure.lean now proves that erasure commutes with expansion, preserving
the focus coordinate, and constructs the focus-preserving bridge from filling
then insertion to the original expanded state. SpecimenTraversal.lean defines
concrete entering/exiting, proves the non-exiting conclusion of Lemma 39(2), and
uses it to synchronize actual search transitions of settled rooted specimens.
The target coordinate is remote and both endpoint states are rooted. Literal
and recursive endpoint renaming are supported. The remaining Lemma 39(3) work
is successor-specimen packaging, allowed-context membership, and the full-UAM
connection. The deep example tests actual traversal and preserves the earlier
non-rootedness obstruction.

`LocalInteraction.lean` and `LocalRewiring.lean` now give an independent
original-graph adjacency and rewiring presentation, proved equivalent to
erasure-based state search in both directions. Recursive endpoint renaming and
determinism are included. `LocalSearchExamples.lean` checks actual variable and
nullary-operation successors.

The finite-pattern milestone completes the formerly second Appendix B item.
`PatternPlugging.lean` constructs the two-edge fragments and proves their actual
plugging equations. `CorollaSearch.lean` factors every search rule through its
interacting edge. `SearchContexts.lean` opens and closes explicit simple hole
contexts, preserving plugging. `HoleContextSearch.lean` proves
`State.search_iff_holeContext` and covers arbitrary simple contexts without
extra assumptions on interaction labels. Regressions include output fragments
and a self-loop whose input and output attachments coincide. **Appendix B now
has four unfinished items after the milestones below.**

The full-UAM milestone clears the transition-definition obligation.
`Substitution.lean` constructs both fragments of Figure 9(f), defines their
application in an actual shallow simple context, and proves mode change and
variable adjacency. `UAM.lean` constrains the extrinsic behaviour to compute
shape and assembles all three transition families into `UAM.machine`.
Search/rewrite and intrinsic/extrinsic exclusion and final normality are proved.
`UAMExamples.lean` checks a two-step terminating execution with variable removal
and a genuine compute transition. Stability of the bound computation belongs
to the remaining rootedness/refocusing proofs, not to the transition definition.

The tuple/safety milestone clears another complete Appendix B item.
`TupleFillings.lean` extracts finite aligned original-hole tuples, proves
pointwise relatedness, distinct names, exact hole coverage, and closed
replacements, and reconstructs recursive specimens from tuple applications.
`ConcreteSafety.lean` defines the full paper quasi-specimen, input-safety,
and robustness predicates, preserving unconditional mode agreement and the
unrooted robustness alternative. Rooted consequences are derived, not assumed.
The nested-box example yields exactly one recorded hole; a mode-mismatched
pair is rejected even with universally true up-to relations.

Estimated completion by mathematical effort: **about 83%**, with a plausible
range of **68–90%**, up from 80% after tuple compatibility and concrete safety definitions.
This is a planning judgment, not a declaration count. Full-UAM structural proofs, specimen packaging, safety, and robustness remain substantial.

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
explicit freshness conditions at arbitrary depth. Nested plugging associativity
and corolla unit laws are now proved. The typed, depth-indexed hierarchy includes explicit binder
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
law is asserted for the chosen transport function. The pointed-host quotient
below identifies structural renaming zigzags. Comparison across
different depth bounds and representation adequacy remain open. The full-UAM structural laws and its
bridge to Theorem 6 remain the main later work.

## Composition and unit milestone

- `Site.comp` explicitly locates a site of an inserted graph in the resulting host.
  `plugAt_assoc` proves arbitrary-depth nested substitution associativity by
  constructing recursive isomorphisms, including at self-loop interfaces.
- `plugAtModuloIso_comp` and `plugAtModuloIso_comp_three` give binary composition
  and three-stage agreement on recursive isomorphism classes.
- Corolla substitution satisfies both unit laws; `plugAt_original` restores the
  original host at any deep site. A selected corolla acts identically on quotient classes.
- `siteRetainedHole_comp` computes the retained inventory of a composed address.
  `plugAt_comp_unique_iff` proves sharp final context closure: the final replacement
  is unique and the two retained inventories and final inventory are pairwise disjoint.
  `Context.plugAtComp` packages this result without demanding intermediate validity.
- Checked regressions cover self-loops, mixed shallow/deep composition, three stages,
  and a duplicate-hole intermediate graph repaired by the second substitution.

These are nested substitution laws. The independent-site and pointed-host
milestone below complements them; the concrete UAM and deep specimen bridge
remain open.

## Independent deep substitution and pointed-host quotient

- PlugInterchange.lean constructs the carrier and incidence isomorphism for
  substitutions at distinct shallow edges, without excluding cycles or self-loops.
- BoxInterchange.lean proves mixed shallow/box interchange and commuting changes
  to distinct box bodies.
- IndependentSites.lean follows structural independence through arbitrary shared
  enclosing boxes. It constructs both residual addresses and a recursive
  isomorphism of the two final graphs, preserves their selected hole labels,
  and proves equality on recursive classes and equivalence of final context validity.
- SiteQuotient.lean quotients typed host/site pairs by finite structural renaming
  zigzags. Substitution, retained-hole inventories, and exact freshness descend;
  the sharp context-validity criterion holds on classes.
- InterchangeExamples.lean checks independent holes inside one box, distinct boxes
  with identical bodies, and the pointed quotient's rejection of a wrong address.
  Intermediate hole-label freshness is not an assumption of interchange.

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
- `Hypernets/Graph/PlugAssociativity.lean`: explicit shallow reassociation isomorphisms.
- `Hypernets/Graph/DeepAssociativity.lean`: site composition, deep associativity,
  exact composite inventories, sharp context closure, and three-stage quotient agreement.
- `Hypernets/Graph/PlugUnits.lean` and `DeepUnits.lean`: corolla units, deep restoration,
  and identity equations on recursive isomorphism classes.
- `Hypernets/Graph/CompositionExamples.lean`: self-loop, collision-repair, and mixed-depth regressions.

The implementation uses Lean's bundled `Std`, with no external library
dependencies. The toolchain is pinned in `lean-toolchain`.

## Mathematical commentary

The [mathematical commentary](docs/mathematical-commentary/main.tex) explains
all 1375 definitions and proved statements in the abstract and concrete graph
development, including regression examples, in mathematical English. Its 1399
source-fragment links point to immutable code revision `3a196f1`. It distinguishes
proved graph properties, conditional specimen results, and the remaining
obligations for the paper's concrete theorem. Appendix A is an alphabetical
glossary of 210 technical terms, with short descriptions and internal PDF links
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

1. Prove representation adequacy and compatibility across depth bounds.
2. Prove substitution preserves rootedness, establish the required full-UAM
   consequences of refocusing, and prove the stationary rewrite criterion.
3. Package synchronized successor coordinates as allowed concrete specimens,
   preserving unique holes and context membership under isomorphism. Construct
   the abstract specimen interface using the checked boundary, non-exiting, and
   settled-search results, and connect its context-step law to the full UAM.
   Prove safety/robustness bridges and initial lifting.
4. Instantiate the checked sufficiency results with all concrete obligations
   discharged to obtain Theorem 6.

The copying UAM, lambda-term translation, and example program equivalences
are later milestones; the current abstract and graph-level examples do not
formalize those parts of the paper.

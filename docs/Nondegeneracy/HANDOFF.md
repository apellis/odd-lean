# Research handoff

Updated 2026-10-25 18:30 UTC. Continue on `research/odd-nondegeneracy` only.

## Standing scope

Continue autonomous parallel research. Maintain upward-to-oriented reduction,
upward independence, and Grassmannian–Webster synthesis. Review and reassign
finished workers; a finished round, pending build, or blocked approach does not
end the research. Keep the progress board current and send per-stream updates.
Stop only for a verified solution, a genuine need for researcher input, or a
hard execution limit. Preserve a precise restart state if execution is cut off.
Do not open PRs against master. Do not merge experimental results piecemeal.

## Baseline and checks

- Baseline commit `0edcf48367872a8edc5563eb781cc777a3ecd227` is pushed.
- Full CI: run `40218574038` completed successfully (baseline `0edcf48`).
- Dependencies in this checkout are copies at the checked-in exact pins. Do not
  run `lake update` or edit external/shared source checkouts.
- Local full build was interrupted when branch CI was dispatched. Targeted
  builds for SKM.Nondegeneracy and the new scoped modules passed.
- All three new Lean result groups have only allowed axioms: arbitrary-skeleton
  normalization, finite oriented coefficient detection, cyclotomic obstruction.
- Python spectral checker and quick exterior checker pass. The exterior
  script's `--action` mode also passed its recorded upward/adjunction tests;
  the later `--full` mode now checks actual 72×72 EF/FE inversion, nonzero square-zero feedback, supernaturality, actual C/D expansions, and normalized odd bubble −δ. Root independently reproduced the complete run.

## Ownership and next steps

| Worker | Owned files / target |
| --- | --- |
| `oriented_choice` | `scripts/Nondegeneracy/MatchingDotFiltration.lean`, `docs/Nondegeneracy/MatchingChoiceTransition.md`, possible `OddMath/SKM/MatchingChoiceTransition.lean`; construct signed choice transition |
| `oriented_sorting` | `OddMath/SKM/OrientedReduction.lean`, matching consumer and note; new distinct closure module if needed; prove evaluated elementary closure |
| `upward_separation` | `OddMath/QuiverHecke/WeightedSeparation.lean`, `docs/Nondegeneracy/UpwardSeparation.md`; refine native straightening |
| `upward_action` | `scripts/Nondegeneracy/nonvacuum_exterior.py`, `docs/Nondegeneracy/ExteriorActionProgress.md`, cyclotomic obstruction module/consumer; actual inversion |
| `webster_synthesis` | `docs/Nondegeneracy/OddUnfurling.md`, new `CoupledBubbleEvaluation` files; coupled bubble formula |
| `rewriting_alternatives` | `docs/Nondegeneracy/RewritingAlternative.md`, spectral and separate adversarial test scripts; challenge assumptions and multicolour overlaps |
| Coordinator | README, this handoff, PROGRESS, cross-review, integration, serial full verification, research-branch commits |

## Mathematical guardrails

- Abstract `SYM` includes distinct odd exterior generators. Spectators do not
  prove that categorical bubbles realize those generators.
- Signed choice transitions lower crossing/open-dot complexity; closure
  transport instead adds dots at fixed crossings. Do not conflate their orders.
- Right coefficient extension uses `d*p`, not `p*d`.
- ELV even-degree constant localization kills that factor's odd parameter.
  This does not prohibit a separate nilpotent reservoir plus invertible probe.
- Squared-dot spectral blocks preserve parity. Ordinary odd-dot scalar
  eigenblock compression is not a multiplicative coefficient detector.
- The known odd intertwiner has norm `-(y²-x²)²(x²+y²)`; its generic transport
  needs both difference and sum units. This is not a universal no-go theorem.
- A triangular bubble substitution needs diagonal units in a fixed probe/base
  algebra, or an explicitly proved invertible earlier-variable substitution.
- The weighted separation paper argument still needs native formalization.
  Complete SKM action and normalized bubble comparison remain separate tasks.

## Current continuation checkpoint

The next signed-column, elementary closure, weighted braid-filtration, and exact exterior-inversion milestones are being integrated. Choice worker continues the coefficient-linear transition; closure worker extends to arbitrary word blocks; separation worker ports dot-down and normal-form induction; action worker builds distinct-colour parity-shifted tensor actions; synthesis worker derives higher bubble coefficients; independent worker tests the connected iji braid. The two-colour connected degree-two pilot has δiδj nonzero but reverse crossing·δiδj zero, so preserve the joint bounded-detection requirement.

## Latest continuation

A brief executor disconnect was resolved and local files/staging were verified intact. No remote divergence was introduced. Commit120463b has full green CI40220230892. Next staged milestones: native MatchingChoiceCoefficients/MatchingChoiceTransition (actual coefficient-space equivalence), RightClosure arbitrary block partial-mate contraction, and WeightedSeparation complete score-controlled PBW straightening. CyclotomicSeparation native pure-power quotient injection built successfully; its concrete consumer check and doc update are pending. New RightMateMatchings remains unverified until worker completes its proof. DotTranslation is under active verification. New disconnected bubble, higher-reservoir, and connected n3/n4 scripts must retain their exact finite scope.

### Superseding checkpoint, 18:30 UTC

`3da1842` now contains choice equivalence, arbitrary-block partial-mate contraction,
and complete weighted affine PBW straightening. Its full CI40221226055 is pending.
Staged next: CyclotomicSeparation and CyclotomicCoefficients (scoped checks and
consumers passed), RightMateMatchings source-cup transport (scoped checks and
nonempty dotted consumer passed), CyclotomicCutoffKernel, higher reservoir pilot,
choice consumer, and paper multicolour cyclotomic analysis with exact scripts.

Active ownership now:
- choice: RightCapAttachment, completing final-cap pairing/reducedness.
- sorting: RightMateMatchings, next coefficient compatibility and full weak-mate family.
- separation: BubbleExterior, actual exterior inclusion/retraction and grading.
- action: N=4 Frobenius action with independent epsilon and delta; bubble normalization.
- synthesis: DotTranslation/OddDotTranslation, native odd-height shifted inverse coordinates.
- alternatives: even-cutoff twisted Mackey map, first connected beta=alpha_j test.

Even cutoffs require a genuine twist: f is normal rather than central, with
nu(x)=x-2d; right multiplication by f uses source right x-action nu-inverse(x)=x+2d.
Odd cutoffs can translate x to x-d, but this does not detect the even-height
odd bubble. Pure-power tensor detection is a module theorem, not a deformed
supertensor algebra or a categorical action. Brundan–Savage isomeric action is
reduced (odd bubble zero), so it cannot by itself supply full exterior detection.

### Superseding checkpoint, 18:35 UTC

Full CI for `3da1842` succeeded. `cd0ba81` pushed with quotient/tensor detection
and source-cup transport; CI40221653309 running. Staged checked next:
BubbleExterior and BubblePolynomialExterior (entire abstract SYM algebra
equivalent to polynomial tensor exterior algebra), RightClosureCoefficients
(source-prefix map has left inverse and commutes with every closed coefficient),
OddDotTranslation local identities and actual inverse coordinates, and exact
vacuum even/odd coefficient detection scripts.

Source review identifies Ebert–Lauda–Vera arXiv2203.14153 Th4.5 as already
constructing the full rank-one deformed action; (4.16) is the twisted P map.
The induced A map has only a lower-degree twisted-linearity defect, not exact
twisted linearity. Prop4.7's explicit bubble computation can be used directly;
its universal-equivalence proof invokes known rank-one nondegeneracy, so do not
use that equivalence circularly. Workers now prioritize the connected extension
and fixed-weight coupling rather than reconstructing the known rank-one theorem.

### Superseding checkpoint, 18:45 UTC

`cd0ba81` full CI40221653309 is green. `c8debb4` is pushed and CI40222091681
is running. Next staged native milestones: PositiveDotTransport's
betaSYM_exists_positiveDotExpansion for arbitrary full coefficients/all colours;
BubbleCoefficientBasis's actual high-weight ideal and quotient injection;
right-cap layer/dot transport; odd braid translation; cyclotomic norm identities.

Current next tasks: choice completes right-cap strand/dot bijection and iteration;
sorting builds UpwardWordTransport then full closure comparison; separation
constructs coefficient-extended QH category using StringDiagrams.Super.BoxProduct
(actual tensor Homs, proved Koszul composition); action investigates disconnected
categorical product coherence after writing fixed-weight rank-one detection;
synthesis audits all-content P/Q projectivity; alternatives checks filtered
Mackey monicity and connected two-bubble pilot. All six remain active.

General-Cartan guardrail: dominant vacua need not be cofinal in a fixed root
coset, and a quadratic-in-head-length cutoff bound does not suffice when head
length grows linearly. Rank-one uses the exact ELV rectangle. A zero-spectrum
deformed reservoir plus compensating generic probes remains a possible Webster
route after the connected action exists; its coupling is not yet proved.

### Superseding checkpoint, 18:54 UTC

`c8debb4` full CI40222091681 is green; `8b5b2cc` pushed, CI40222830590 running.
Staged checked: CoefficientExtension (BoxProd actual signed tensor category),
UpwardWordTransport, ClosureCoefficientExpansion (actual partial-mate closure
with full coefficients and positive-dot errors), final right-cap/suffix
matching/decorator/layer transport, source projectivity notes, fixed-weight
rank-one argument, and finite disconnected categorical product pilot.

Reallocated ownership: rewriting_alternatives now proves cyclic pairing
reindexing/coverage in coordination with choice. Choice owns WeakMateMatchings
and WeakMatchingChoice; sorting owns UpwardTopDots and independence transfer.
Use all-top upward dot serializers: positive appended dots then reorder exactly
without crossing slides, preserving strict dot increase. Do not use the general
choice lower-dot comparison inside the least-dot closure detector; transfer
weak-to-strict independence separately by its lower-lex triangular surjection.
Separation owns WeightedCoefficientSeparation; synthesis audits Section 9
inversion after the proposed Section 8 projectivity argument; action writes
all-cutoff disconnected product coherence following the finite joint pilot.

Source Section 8 correction: obtain monic square-variable annihilators from
conjugate fbar*f and KKO7.3 independently of PQ. Restrict to central s=t²,
which the P twist fixes. This avoids circular use of PQ for projectivity.
Section 9 negative-height recurrence shifts psi as well as phi; shifted cap
rows require a unitriangular conversion to the actual dotted rows.

## Workspace-disconnection recovery checkpoint (2026-10-25)

The executor became unavailable after the 19:01 UTC checkpoint. Local Lean
and Python execution is paused; source-level research continues. This note
was saved through GitHub and is the only remote-only change. On restoration,
fetch and fast-forward the research branch before making the next commit,
preserving the existing staged and unstaged research files. Do not reset or
clean the checkout.

Last pushed code: `901938ca7cb742e43f5d4e0ee6e03a2d35f51d38`.
CI40222830590 for `8b5b2cc`: completed/success.
CI40223506675 for `901938c` was running at the last check.

### Checked locally and staged after that code commit

- WeightedCoefficientSeparation and its consumer: actual signed weighted
  relation-ideal separation, deformed polynomial membership, joint quotient
  detection. Its existing consumer is generic; root requested an additional
  concrete two-odd-colour rational nonzero-image example.
- PairingRotation and consumer, including suffix pairing reflection and
  reverse cyclic strict realization.
- WeakMatchingChoice, WeakMateMatchings, and WeakMatchingChoice consumer:
  genuine weak-to-strict independence transfer by a surjective triangular map.
- UpwardTopDots and consumer; PositiveClosureDetector and consumer.
- Expanded disconnected_tensor_action.py and DisconnectedTensorAction.md:
  full finite degree-two weight window, actual same/mixed inversions,
  adjunctions, supernaturality, and nonzero product of two actual odd bubbles.
- Updated MatchingChoiceTransition, OrientedReduction, UpwardSeparation,
  MulticolourActionTheorem, and CoupledBubbleEvaluation notes. The action
  manuscript is explicitly PROPOSED, not a checked native action theorem.

### Unfinished local continuation

- choice: TopMatchingChoice core/top dots bridge checked; final length lemma
  and consumer were being checked. Combined weak-family coverage and native
  detector assembly remain. WeakMateMatchings is already staged.
- sorting: TopClosureCoefficients.topPositions_perm_counts checked;
  appending top_correction_signed was interrupted and may not have landed.
  Need supported finite correction labels and the actual independence transfer.
- rewriting: WeakMateCoverage file saved and elaborated; only reported errors
  are unused simp arguments `up,dn` on line35. Remove those two simp arguments,
  rebuild, then export. BubbleCoefficientParity is agreed next ownership but
  not yet created: explicit coefficient-basis diagonal parity involution and
  source/target beta placement identity.
- separation: new WeightedDeformationIdeal composition closure and
  high-coefficient identity compiled. BubbleCoefficientGenerators elementary
  weight proofs have an unverified final fix; attempted singleton-delta patch
  did not land. Concrete rational weighted consumer is pending.
- synthesis: native negative-height cap-row conversion patch failed on its
  first tool call; no edit/build claim. Proposed all-content even-cutoff
  action manuscript is saved/staged. Its left-projectivity argument uses
  opposite coefficients with d'=-d^op, not a specialization-preserving
  involution assumed without proof.
- action: spectral compensation review continues. Nonzero probes are not
  isolated A1 components globally. Candidate weighted coroot folding has
  factor2 for nonzero odd-colour fibres and factor1 for even colours; the
  zero odd component retains factor1. This remains a target for categorical
  comparison, not an established coupling.

### Exact next priorities

Resume scoped builds, finish source/target coefficient parity and sorted-boundary
independence assembly, then contextual sorting for arbitrary boundaries. Extend
weighted separation to specific coefficient quotient ideals. Independently
review and implement the proposed connected action; spectral/unfurling coupling
and fixed-weight coverage remain separate. Maintain all three streams and
immediately reassign completed workers. No PRs against master.

### Connection restored

The executor returned; `git fetch` and `git merge --ff-only` incorporated
recovery commit `4b16af0` with all staged/unstaged work intact. Workers resumed.
No remote/local divergence remains. Do not treat the earlier outage as an
active blocker. WeightedCoefficientSeparation and the weak matching/rotation/
positive-dot checkpoints are staged for the next research commit.


## Integrated continuation checkpoint

CI for `901938c` passed; `15ad5c1` is running separately. The executor is
available and all six workers continue. No full nondegeneracy theorem is claimed.

- Oriented: full-SYM parity placement equivalence, canonical positive-dot
  coefficient lift, weak mate coverage and literal layers are scoped checked.
  Choice assembles sorted independence; sorting audits its hypotheses and then
  owns contextual assembly; rewriting supplies list-boundary wrappers; Webster
  proves actual local paired-sector pivots and recurrences.
- Upward: weighted signed quotient detection is integrated. Explicit ELV
  coefficient specialization and its generated quotient bounds are next.
  These results concern affine coefficient-extended quotients, not yet an SKM action.
- Synthesis: the actual 80 by 80 fixed-weight reservoir/probe mate passes,
  retaining odd and even coefficient products. General weighted spectral folding
  and the proposed connected action still require categorical justification.

Next review checkpoint: sorted theorem hypotheses, all-weight paired sorting,
ELV quotient consumers, and reproducible fixed-weight coupling computation.
All work remains on `research/odd-nondegeneracy`; no master PR.


## Sorted-boundary milestone

`WeakMate.sorted_independence` now builds: full upward matching-expansion
independence implies every sorted oriented matching family is independent, at
every prescribed external weight, over full SYM. The top serializer, ordinary
layers, weak mate coverage, closure correction and coefficient parity premises
are all discharged. Independent assumption audit found no additional action,
field, finite-colour or bubble-faithfulness hypothesis. This is not yet the
full arbitrary-boundary implication.

The remaining oriented work is actual local exchange descent. Global boundary
induction is checked conditionally; paired crossing expansions are checked;
workers are constructing contextual adapted families and their coefficient maps.

`UpwardCoefficientDetection` isolates finite observations at fixed weight as a
sufficient condition for the actual affine coefficient evaluation to be injective.
Neither these observations nor its PBW-to-matching comparison is yet constructed.
The latter is now the separation worker's task.

The 80 by 80 fixed-weight coupling script was independently reproduced. The
general synthesis still needs actual categorical coupling and bubble recovery.
We are also testing a simpler route using two original-superdatum cyclotomic
actions with disjoint zero/nonzero spectra, before committing to a weighted
Clifford-to-even cover construction.

CI for `15ad5c1` passed; `67c4365` is running. Research branch only.


### Integration and continued assignments

CI `40225381594` for `67c4365` caught an umbrella-only name collision:
new `QuiverHecke.cl_nil` duplicated the declaration in `Centre`. Renamed the
new helper `coefficient_cl_nil`; the full local build is running. Scoped
checks, including the sorted theorem's populated consumer and standard axiom
audit, pass. The next commit is a checked local checkpoint awaiting full CI.

Worker allocation now: choice + separation construct the canonical affine
PBW/matching evaluation bridge; sorting + rewriting + Webster assemble actual
contextual source/target exchange; action develops the direct disjoint-spectrum
coupling. All six continue. The original all-content action remains a proposed
manuscript. The direct coupling has a symbolic Frobenius-pairing argument at
the highest probe vacuum; general coupled inversion remains under investigation.

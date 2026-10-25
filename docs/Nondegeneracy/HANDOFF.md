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

# The supported upward module action

Brundan–Ellis Definition 1.5 and (2.6) prescribe the relations and the
resulting upward module action. `SwappedAssembly/SupportedAction.lean`
assembles these obligations for the chosen cyclotomic probe–reservoir
construction on supported Hom inputs, the F4 step of
[SwappedActionAssembly](SwappedActionAssembly.md).

`SupportedSectors.pointwiseObligations` uses the prescribed
`pointwiseLeftwardData`. The quadratic, slide, braid and zigzag
relations are the corresponding factor and sector assemblies, with
the constructed mixed crossing inverse and denominator units. The
window-zero relation is the retained support window. Inversion uses
`inversionRelations_of_supportedInverse` and the proved pointwise
inverse at every supported input reached by a context path.
Interchange uses `pointwiseLeftward_interchangeLaw` on the same
supported inputs.

The intermediate `pointwiseObligations_of_sigmaPermutation` separates
the distinct-colour permutation input. In the final theorem this input
is `CyclotomicAction.elvProbeSigmaPermutation`, whose four entries are
proved for the specified construction. Its pure probe input is the
canonical factor left-mate theorem, derived from the cap and cup
pitchfork identities. Thus the final obligation theorem has no
additional permutation, factor-mate or action premise. In particular,
equal-colour inverse identities are required on the supported objects
reached by paths, rather than throughout an unrestricted Hom category.

`SupportedSectors.pointwiseUpwardModuleAction` applies the resulting
presentation obligations to obtain `UpwardModuleAction D Sc μ`.
Subsequent vacuum observations may use this action; their faithfulness
or nondegeneracy conclusions are separate statements.

The paired consumer uses the weighted Boolean datum with an odd
colour, a tensor source word containing both colours, and the vacuum
target family. It constructs the content-dependent bound and every
datum, parameter, cutoff and support input, then applies both the
obligation theorem and the resulting module-action constructor.
Nonzero probe append vectors in both colours are retained. Its audit
checks all owned declarations of the supported inversion,
supernaturality and action modules against the standard axiom
allowlist.

The stronger consumer `scripts/NonVacuity/SupportedTensorAction.lean`
uses the two-odd collision datum with off-diagonal Cartan entries
`-2`, symmetrizer one and homogeneous parameters with zero interior
coefficients. The source word contains both odd colours. Its nonempty
reservoir content has root weight zero, so weight alone cannot identify
the source sector with the vacuum sector. Bounded coordinate
injectivity proves that the product of the two odd coefficient
generators is nonzero in the selected tensor row. This proves that the
source object, the full tensor matrix vacuum and the corresponding
vector in the complete action's module are nonzero. The same source
and target families supply all presentation obligations, and the
identity diagram acts nontrivially on this vector. The consumer audits
both imported mathematical modules and the constructed nonzero-vector
proofs.

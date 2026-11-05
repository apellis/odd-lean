# Inverse column moments at positive height

Toward `SwappedVacuumEvaluation.bubbles_eq` (critical chain item 2,
derivation in `SwappedVacuumBubbles.md` §§2–4). Lean:
`OddMath/QuiverHecke/SwappedVacuum/InverseColumnMoments.lean`.

## Setting

Positive height `H > 0`, reservoir level `N > 0`, probe degree `P = H + N`.
Maps `s : X ⟶ Y`, `v : X ⟶ V`, `u : V ⟶ Y`, reservoir cap `ell : Y ⟶ V`,
dots `x : End X`, `y : End Y`, slide `s ≫ y - q • (x ≫ s) = v ≫ u` with
`q * q = 1` (`q = 1` even, `q = -1` signed odd). The extreme column `a`
of the inverse of the augmented matrix `[s; v; v x; …; v x^(H-1)]` gives

* `a ≫ s = 0`,
* `a ≫ x^j ≫ v = δ(j, H-1)` for `j < H`,

and the reservoir window `u ≫ y^i ≫ ell = δ(i, N-1)` for `i < N`
(`tensorPowerVacuumCap_window`). The probe is monic of degree `P`:
`Σ_{n ≤ P} c_n x^n = 0`, `c_P = 1`.

## Proved (checked locally with warnings as errors)

* `column_slide`: for all `n, d`,
  `a ≫ x^n ≫ s ≫ y^d ≫ ell = -Σ_{j<n} q^(n-j) (a ≫ x^j ≫ v) ≫ (u ≫ y^(d+n-1-j) ≫ ell)`.
* `reservoir_mul_weightedColumn` (ring form) and
  `inverse_column_reservoir_series` (categorical form): with column moments
  `b_j = a ≫ x^j ≫ v`, reservoir moments `T_l = u ≫ y^(N-1+l) ≫ ell` and
  `G_l = Σ_{n ≤ P, n + l ≥ N + 1} c_n b_(n+l-N-1)` (`weightedColumn`),

  `Σ_{l ≤ L} (q^l G_l) ≫ T_(L-l) = δ(L, 0)`.

  Writing `B_m = b_(H-1+m)` (normalized left bubble moments) and
  `ĉ_r = c_(P-r)`, `G = ĉ · B` as power series. Hence `B` is determined
  by the reservoir moments: the `q`-twist of `ĉ · B` is the inverse of `T`.

* `weightedColumn_eq_sum` and `reservoirSeries_mul_probe_mul_column`
  (`InverseColumnSeries.lean`): as power series,
  `T(z) · ĉ(z) · B(qz) = 1` with `ĉ_r = c_(H+N-r)`, provided
  `q^r ĉ_r = ĉ_r`. `square_add_one_reversed_support` supplies this for the
  odd probe `(x² + 1)^M`, `q = -1`; it is trivial for `q = 1`.

No support condition on the probe is needed for the coefficient identity (the `q^n s ≫ y^n` term is
killed by `a ≫ s = 0`); the high-degree terms of the probe relation
(`Σ c_n b_(n+m) = 0`) cancel the coefficients `l > N`.

## Odd colours: the substituted series

`odd_inverse_column_moments` (`InverseColumnOddSeries.lean`) solves the series
identity at an odd colour. If the reservoir moments are
`T(z) = A(z²)(1 + e z)` with `A(w) = 1/C(-w)` (mapped along an algebra map
`φ` out of the polynomial generators) and `e² = 0`, the probe is
`(x² + 1)^M` with `H + N = 2M`, and `q = -1`, then

  `B(-z) = (1 - e z) · (C(-w)(1 + w)^(-M))|_(w = z²)`,

so `B_(H-1+2s)` is `φ` of the `s`-th coefficient of
`VacuumSeries.substitutedSeries k (SYM.probeSeries D k M) i` (the right side of
`AdjunctionBubbleSeries.left_odd`) and `B_(H+2s)` is `e` times it. No
commutation of `e` with the polynomial coefficients is used.
`mk_eq_expand_mul_one_add` turns the coefficientwise moments
`T_(2r) = φ(a_r)`, `T_(2r+1) = φ(a_r) e` into the series hypothesis; these are
the shapes of `tensorPowerVacuumCap_moment_even` and
`tensorPowerVacuumCap_moment_odd`, with `e = (-1)^(N+1) δ`.

## Even colours: the substituted series

`InverseColumnEvenSeries.lean` treats `q = 1` with the even probe
`(x - 1)^P`, `H + N = P`. The reversed probe coefficients are `(1 - z)^P`
(`reversed_sub_one_pow`), equal to the inverse probe series at an even
colour (`probeSeriesInv_even`). If the reservoir moments `T_(N-1+l)` are the
coefficients of `A = 1/E(-z)` mapped along `φ`, then
`even_inverse_column_moments` gives `B_(H-1+s) = φ(coeff s (substitutedSeries
(probeSeries P) i))`, the right side of `AdjunctionBubbleSeries.left_even`.
The proof is the odd argument with `e = 0`.

## Tensor vacuum and the actual positive inverse

`ELVTensorVacuumColumnMoments.lean` instantiates the odd identity on the
tensor vacuum. `tensorVacuumEndDecode` evaluates an endomorphism of the
vacuum value at the vacuum point and conjugates by the decode chart.
`tensorVacuumColumn_odd_moments` takes any column `a` with
`a ≫ evaluatedMixedBend = 0` and `a ≫ x^j ≫ v = δ_(j,h-1)` for `j < h`
(`x` the shifted pre dot, `v` the shifted pre cap) and gives the decoded
moments `a ≫ x^(h-1+2s) ≫ v` and `a ≫ x^(h+2s) ≫ v` as left multiplication
by the substituted-series coefficients of `left_odd`, the latter times
`(-1)^(N+1) δ`. `tensorVacuumCapInverse_odd_moments` reads both column
hypotheses off an `IsCapInverse` of the bend with windows `x^n ≫ v`.

The actual inverse supplies such an `IsCapInverse`.
`posMap_isCapInverse_of_zero_corners` (`CentralInverse/PositiveVacuumWindow.lean`)
restricts the inverse of the positive two-sector matrix to the surviving cap
window when the reservoir source and probe target are zero.
`vacuumCapInverseData` (`Sigma/VacuumCapInverseWindow.lean`) applies it to the
prescribed positive factor matrix at formal content zero, which
`centralFactorMatrix_content_isIso` makes invertible for nonnegative height.
Its principal entry and columns are literal entries of that inverse
(`vacuumCapInverseData_principal`, `vacuumCapInverseData_window`). Its
windows are the native probe caps `centralPaddedCap true n`.

## Attachment to the vacuum adjunction (odd colours, positive height)

`ELVProbePaddedVacuumCap.lean` identifies the prescribed padded cap rows
`centralPaddedCap true n` at the vacuum sector with the native `x^n ≫ v`
of the output block (`paddedVacuumCap_native`), through the same source
chart as the padded Dx entry and the target chart
`paddedVacuumCapTargetIso`. `vacuumPreReservoirCap_native` does this on the
regular probe for every dotted reservoir cap, without parity.

`ELVProbePaddedVacuumCapInverse.lean` transports `vacuumCapInverseData`
entrywise (`IsCapInverse.map`, `.coordinates`, `.target`) to the native
chart: `vacuumCapInverse_native_odd` is a cap inverse of
`[evaluatedMixedBend; x^n ≫ v]_(n < h)` for the vacuum bend block of any
input equal to the supported vacuum input.

`ELVTensorVacuumCapInverseAttach.lean` takes the input to be the tensor input
(`tensorSectorInput_eq_supported`), whose empty output block is the tensor
vacuum probe functor (`tensorOutputAt_empty`), and the window length
`h = P_i - N_i` (`vacuum_positive_window_length`). For an odd colour with
`0 < N_i < P_i`, `tensorVacuum_chosenCapInverse_odd_moments` gives the chosen
inverse `(j, A)` and the substituted-series moments of its last padded column
`A (h-1)`. The column-moment step itself goes through the generic
`column_moments_of_slide` (slide relation, probe polynomial and both windows).

## Remaining for item 2

Checked on `research/positive-bubble-field`:

- `ProbeReservoir.evalW_apply_whisker`,
  `ProbeReservoir.res_opList_ext_whisker_apply` (`WhiskerEvaluation`): entries of
  the native layer evaluation of a whiskered diagram, also up to equalities of
  boundary objects.
- `SPath.append_nil_nil_cast` and `pointwiseUpwardModuleAction_act_bubAt_cl`
  (`SupportedClosedAction`): the supported action of `bubAt` of a closed diagram
  on `ob μ (upWord t)` postcomposes each matrix entry with the path functor of
  the closed diagram's `compDiag` on empty paths at the target sector.

- `entryEquiv_comp_map`, `pointwiseUpwardModuleAction_act_bubAt_cl_eq`,
  `pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient`
  (`SupportedClosedCoefficients`): a closed diagram acts on the tensor-family matrix
  module as the source coefficient `a` once its vacuum-sector entry is the vacuum
  coefficient action of `a`; off-vacuum sectors are zero objects.
- `SKM.inv_smul_bubLs_of_pos` and
  `pointwiseUpwardModuleAction_act_bubAt_bubLs_eq_coefficient`: at `hᵢ(μ) > 0`,
  `c⁻¹·bubLs(s) = cl (dcupL i (h-1) ++ epsL i (s+h-1))`, so the `left_odd` and
  `left_even` fields reduce to the vacuum entry of this closed diagram.

- `isCapInverse_centralPadded_of_posInverseAt` (`Sigma/PointwiseCapInverse`): a
  pointwise `PosInverseAt` at a central sector gives an explicit cap inverse of the
  padded cap, with columns the evaluated leftward cups composed with the source
  factor and corner isomorphisms.
- `compDiag_dcupL_epsL_swappedGens`, `map_dcup_epsEntry_eq_padded`
  (`Sigma/PointwiseBubbleEntry`): the swapped-generator entry of
  `dcupL i n ++ epsL i N` on empty paths is `dcup ≫ epsEntry`, and its evaluation
  is the leftward column composed with the padded cap.
- `vacuumLeftwardColumn`, `vacuumLeftwardCapInverse_native_odd`,
  `vacuumLeftwardColumn_cap_native` (`ELVProbeLeftwardVacuumCapInverse`): at the
  vacuum sector input these columns are a cap inverse of the native mixed bend,
  and `column ≫ dot^N ≫ cap` is the conjugated evaluation of the bubble entry.
- `vacuumLeftwardCapInverse_bubbleEntries`, `tensorVacuum_leftward_odd_moments`
  (`ELVTensorVacuumLeftwardMoments`): at the tensor vacuum the leftward cap inverse
  has the substituted-series moments of `tensorVacuumCapInverse_odd_moments`, so
  the conjugated evaluated entries `dcup (h-1) ≫ ε x^(h-1+2s)` and
  `dcup (h-1) ≫ ε x^(h+2s)` decode to multiplication by the substituted-series
  coefficient (times the reservoir odd coefficient in the second case).

Still open:

1. Vacuum entry (remaining part): lift the identity of
   `tensorVacuum_leftward_odd_moments`, which holds after vacuum sector evaluation,
   conjugation and decoding, to the equality in `End(tensorVacuum)` required by
   `pointwiseUpwardModuleAction_act_bubAt_bubLs_eq_coefficient` (with
   `dc = pointwiseLeftwardData.dcup` from `centralPointwiseLeftward_posInverseAt`,
   and `compDiag_dcupL_epsL_swappedGens` for the entry). Two inputs are needed:
   the evaluated, conjugated and decoded coefficient action of `a` is
   multiplication by the image of `a`, and an endomorphism of `tensorVacuum` is
   determined by its decoded evaluation at the regular probe object
   (faithfulness of the vacuum sector evaluation on that endomorphism space).
   The generic Yoneda step is checked (`ELVVacuumTensorFaithful.lean`):
   `VacuumTensor.hom_ext_of_generating` and `hom_ext_of_generating_total` show
   that a transformation out of `G` followed by the tensor vacuum `M ↦ W ⊗ M(a)`
   is determined by its component at one object `Y₀`, when every homogeneous
   vector of every `(G X)(a)` is `(G f)(y₀)` for a fixed `y₀` and a homogeneous
   `f : Y₀ ⟶ X` of the same parity (here `G = emptyProbe`, `Y₀ = regularProbe`).
   The generating hypothesis is checked (`ELVRegularProbeGenerating.lean`):
   `regularProbe_generating` gives, for every homogeneous vector `n` of the
   empty block of a probe weight product `Y`, a morphism
   `regularProbe ⟶ Y` of the same parity carrying `regularVector` to `n`.
   It uses that the old empty-content category has only the empty object
   (`emptyObject_eq`), that its endomorphisms are coefficients
   (`vacuumEnd_eq`, `vacuum_map_eq`), and the morphisms `vacuumHom` out of the
   regular empty probe. Faithfulness is checked
   (`SupportedVacuumDecodeFaithful.lean`): `WeightTensorVacuum.selectedHom_end_ext`
   determines an endomorphism of the selected Hom input by its total at
   `regularProbe` on the vacuum block (off-vacuum blocks are zero objects),
   `tensorVacuumEndDecode_injective` holds since the content-zero category has one
   object, and `SupportedSectors.vacuumDecodeFaithful_tensorTarget` gives, for every
   comparison `c : E Z ≅ V`, injectivity of
   `f ↦ tensorVacuumEndDecode (c.inv ≫ E.map f ≫ c.hom)` on endomorphisms of the
   vacuum object `Z` of the tensor target family, `E = vacuumSectorEvaluation`.
   The coefficient reading is checked (`SupportedVacuumCoefficientDecode.lean`):
   `SupportedSectors.vacuumDecode_tensorTargetCoefficient` shows that for every
   comparison `c : E Z ≅ V` whose forward map is an `eqToHom`, the vacuum coefficient
   `tensorTargetFamilyCoefficientAction (0,0) a` decodes to left multiplication by
   `coefficientPowerQuotientMap a` (the `hcoef` hypothesis of
   `vacuumEntry_of_decode`). Its core is
   `VacuumTensorCoefficientMaps.selectedVacuum_coefficient_endDecode`, from
   `sourceCoefficientAction_tensorVector` at the vacuum block.
   The leftward odd moment identity now returns its comparison as an `eqToHom`
   (`tensorVacuum_leftward_odd_moments`, #1090). Item 1 is then assembled in
   `SupportedLeftVacuumEntries.lean`: `SupportedSectors.vacuumLeftOdd_decode`
   evaluates the vacuum entry of `dcupL i (h-1) ++ epsL i (2s+h-1)` through
   `compDiag_dcupL_epsL_swappedGens` and the moments, and
   `SupportedSectors.vacuumEntry_left_odd` gives the `VacuumEntry` with coefficient
   `coeff s (substitutedSeries (probeSeries m) i)`, for odd `i`, `0 < cutoff i` and
   `0 < h = ⟨hᵢ, ν₀⟩`. Item 2 is in the same module:
   `SupportedSectors.vacuumEntry_oddBubble` gives the entry of
   `dcupL i (h-1) ++ epsL i h` with coefficient `probeSign cutoff i • δᵢ`. Both use the
   cutoff of the tensor target family as `N`; the route transport identifies it.
2. The odd bubble `oddBubble` at positive height, the same way.
3. Even colours: `ELVTensorVacuumLeftwardEvenMoments.lean` gives the even moment
   identity `tensorVacuum_leftward_even_moments` (from the generic
   `even_column_moments_of_slide`, the probe polynomial `(x - 1)^m`, the even central
   slide and the reservoir series `1/E(-z)`), and
   `SupportedSectors.vacuumEntry_left_even` the entry of
   `dcupL i (h-1) ++ epsL i (s+h-1)` with coefficient
   `coeff s (substitutedSeries (probeSeries m) i)`. Nonpositive height is handled
   separately.
4. Transport from `actionAt (probeHW - reservoirHW)` and the restricted datum to the
   route index to conclude `PositiveBubbleField (swappedRouteBases sy)`. The assembly is
   checked (`VacuumRouteSwappedPositiveBubbles.lean`): `SKM.oddBubble_eq_cl_of_pos`
   writes the odd bubble at positive height as `cl (dcupL i (h-1) ++ epsL i h)`;
   `VacuumBubblesPositiveHeight.of_closed` gives the positive-height hypothesis
   for any upward action from the values of its closed action on these
   diagrams; and `positiveBubbleField_of_entries` concludes the field from
   `SwappedLeftEntriesField sy`, the vacuum entries
   `SupportedSectors.VacuumLeftEntries` at every route index (with
   `M = probeExponent`, `N = reservoirLevel`). With the right entries,
   `nondegeneracy_of_swapped_entries` gives the conjecture. The entries are discharged
   in `VacuumRouteSwappedPositiveField.lean`: `SupportedSectors.vacuumLeftEntries`
   assembles items 1–3 at the vacuum weight `ΛP - ΛR` (`tensorVacuumWeight`), the
   route weight is `probeHW - reservoirHW` (`weight_difference`), and the reservoir
   levels are positive (`VacuumRouteIndex.level_pos`, from `cutoff_bounds`). So
   `swappedLeftEntriesField` and `positiveBubbleField_swappedRouteBases` hold with
   no hypothesis, and `nondegeneracy_of_swapped_right_entries` reduces the
   conjecture to `SwappedRightEntriesField` (nonpositive height).

5. **Right vacuum entries, reduction to the probe reservoir.**
   `VacuumRouteSwappedNonpositiveField.lean` mirrors item 4 for `SwappedRightEntriesField`:
   `RightVacuumEntrySupply` asks for `SupportedSectors.VacuumRightEntries` of every probe
   reservoir with positive probe cutoffs and reservoir levels, at the vacuum weight
   `ΛP - ΛR`; `swappedRightEntriesField_of_supply` transports it along
   `weight_difference`, and `nondegeneracy_of_rightVacuumEntrySupply` gives the conjecture.
   The probe cutoffs of every route index are positive (`VacuumRouteIndex.probeCutoff_pos`,
   from `cutoff_bounds`), so for odd colours `M > 0` and the case `M = 0` does not arise
   in the odd right entries. The supply is open: its six families are the negative-height
   entries (even moments, odd moments, odd coefficient) and the zero-height entries.

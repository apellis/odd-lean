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

1. Identify the normalized presentation bubbles `c⁻¹·bubLs(2s)` with these
   column moments to produce the `left_odd` field.
2. Even colours and nonpositive height are handled separately.

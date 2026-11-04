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

## Remaining for item 2

1. Instantiate `t`, `b`, `φ`, `e` on the tensor vacuum: `t` from
   `tensorUnitCapClosure` (as left multiplication by its moment after the
   decode chart), `b` from the chosen inverse column
   (`ProbeWindow.IsCapInverse`) and the padded unit columns, checking the
   slide and window hypotheses for the actual maps.
2. Identify the normalized presentation bubbles `c⁻¹·bubLs(2s)` with these
   column moments to produce the `left_odd` field; the odd coefficients give
   the odd bubble.
3. The same instantiation for even colours (series step done above) and
   the other heights.

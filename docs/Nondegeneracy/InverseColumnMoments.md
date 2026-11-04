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

## Remaining for item 2

1. Identify `T` with the raw coefficient moments of the reservoir
   (`signedMoment_recurrence`), so that `T(z)⁻¹` is the coefficient series
   `C_i(-z)` (odd) or `E_i(-z)` (even) of `AdjunctionBubbleSeries`, and
   match `ĉ(z)·B(qz)` with `(1+z²)^M · B(-z)` (odd) or `(1-z)^P · B(z)`
   (even).
2. Attach `a` and its window to the actual inverse column
   (`ProbeWindow.IsCapInverse`) and the padded maps, producing the
   `left_even`/`left_odd` fields of `AdjunctionBubbleSeries`.

# Nonpositive-height bubbles as reciprocal series

> The Nondegeneracy Conjecture in the research scope is proved in Lean (`nondegeneracy_of_symmetrizer`; see
> [STATUS](STATUS.md)). Steps described below as open, pending or conditional are either
> proved among that theorem's dependencies or belong to routes it does not use.

This note extends [InverseCapMoments](InverseCapMoments.md) and
[NegativeCapInverse](NegativeCapInverse.md) from single moments to the
generating series of [SwappedVacuumNonpositiveBubbles, §§3–4, (11)–(14)](SwappedVacuumNonpositiveBubbles.md),
for research issue #345 (Brundan–Ellis, *Super Kac–Moody 2-categories*, §8).

Notation as in InverseCapMoments: slide `y s - q s x = v u`, monic probe
`g = Σ c_n T^n` of degree `P` with `c_n q^n = c_n` and `g(x) = 0`, and
reservoir moments `t_n = u y^n ell`, zero below `N-1` with `t_(N-1) = 1`.

## Abstract statements (`InverseCapSeries.lean`)

* `probe_cap_convolution`: reindexing `n ↦ P-n` turns
  `Σ_n c_n t_(n+m)` into the degree-`l` coefficient of `ĉ(z)·T(z)`, where
  `ĉ_r = c_(P-r)` is the reversed probe and `T(z) = Σ_l t_(N-1+l) z^l`.
* `negative_inverse_cap_moment`, `negative_inverse_cap_series`
  (height `H < 0`, `N > P`): for the extreme inverse cap `b` of
  NegativeCapInverse, the moments `u y^(N-P-1+l) b` form the series `ĉ·T`.
* `zeroHeightMoment`, `zero_height_moment`, `zero_height_series`
  (height `0`, `N = P`, `j = s⁻¹`): with the fake moment `K_0 = 1` and
  `K_l = u y^(l-1) j v` for `l ≥ 1`, `Σ K_l z^l = ĉ·T`. The `l = 0` case is
  `c_P t_(N-1) = 1`, proved separately from the `l ≥ 1` cases.

## Colour specialisations (`InverseCapColourSeries.lean`)

Assume `φ(T) = (1 + e z)·φ(expand₂ R)` (odd) or `φ(T) = φ(R)` (even), where
`R = 1 / C(-z)` (resp. `1 / E(-z)`), as established for positive height in
#1051–#1053. Then `ĉ = expand₂((1+X)^M)` (odd, `g = (X²+1)^M`, `q = -1`) or
`ĉ = (1-X)^P` (even, `g = (X-1)^P`, `q = 1`), and `momentSeries` of
`probeSeriesInv` is `(1+z)^M/C(-z)` (resp. `(1-z)^P/E(-z)`). Hence:

* `odd_cap_moments`, `even_cap_moments`: the series identity in coefficient form.
* `odd_negative_cap_bubbles`: `u y^(N-2M-1+2r) b = φ(m_r)`,
  `u y^(N-2M-1+2r+1) b = φ(m_r) e`.
* `odd_zero_height_bubbles`: `u y^(2r) s⁻¹ v = φ(m_r) e`,
  `u y^(2r+1) s⁻¹ v = φ(m_(r+1))`; in particular the odd degree-zero bubble is `e`.
* `even_negative_cap_bubbles`: `u y^(N-P-1+l) b = φ(m_l)`.
* `even_zero_height_bubbles`: `u y^l s⁻¹ v = φ(m_(l+1))`.

Here `m_r` is the `r`th coefficient of the momentSeries. No relation
`e² = 0` and no commutation of `e` with `φ` is used. The reservoir series
hypothesis `hT` is an input. Discharging it at `H ≤ 0` from the positive-height
reservoir computation is the remaining step for `bubbles_eq` at nonpositive height.

## On the tensor vacuum

`ELVTensorVacuumCapMoments` instantiates the odd results on the prescribed
tensor vacuum with `x` the shifted pre dot, `y` the evaluated post dot, `s`
the A6 bend, `u` the adjunction unit, `v` the shifted pre cap and `ℓ` the
reservoir cap, probe exponent `M = m i` and cutoff `N = cutoff i`. The
reservoir series hypothesis is discharged by `tensorPowerVacuumCap_moment_even/odd`
(`e = (-1)^(N+1) δ`), in the decode chart `tensorVacuumEndDecode`:

* `tensorVacuumNegativeCap_odd_moments_even`, `_odd` (`2M < N`, any cup inverse `[j; B]`):
  `u y^(N-2M-1+2r) B_(N-2M-1) = A_r`, `u y^(N-2M-1+2r+1) B_(N-2M-1) = e A_r`.
* `tensorVacuumZeroHeightCap_odd_moments_even`, `_odd` (`2M = N`, bend an isomorphism):
  `u y^(2r) s⁻¹ v = e A_r`, `u y^(2r+1) s⁻¹ v = A_(r+1)`.

Here `A_r` is the `r`th coefficient of `(1+w)^M/C(-w)` acting on the
coefficient chart.

At an even colour the reservoir moments are the complete coefficients:
`ELVCoefficientPowerEvenColourSeries.even_colour_signedMoment` proves
`signedMoment (N-1+r) = h_r`, the `r`th coefficient of `1/E(-z)`, from the
cyclotomic recurrence of the raw moments (the remainder polynomial is the
reversed `E(-z)`). With the even slide (`koszulSign 0 0 = 1`) and the probe
polynomial `(x - 1)^M = 0`, `SwappedVacuum.even_cap_moments` gives, with `A_l`
now the `l`th coefficient of `(1-w)^M/E(-w)`:

* `tensorVacuumNegativeCap_even_moments` (`M < N`, any cup inverse `[j; B]`):
  `u y^(N-M-1+l) B_(N-M-1) = A_l`.
* `tensorVacuumZeroHeightCap_even_moments` (`M = N`, bend an isomorphism):
  `u y^l s⁻¹ v = A_(l+1)`.

Still open at `H ≤ 0`: existence of the cup inverse and of the zero-height
inverse, the case `M = 0` (the bend needs `0 < probeCutoff`), the
identification of `momentSeries (probeSeriesInv)` with the `substitutedSeries`
in `VacuumBubblesNonpositiveHeight`, and the attachment to `bubLs`.

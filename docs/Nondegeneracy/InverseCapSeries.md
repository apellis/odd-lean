# Nonpositive-height bubbles as reciprocal series

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

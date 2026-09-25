import OddMath.Diagrams.OddNilHecke.DifferentialLongest
import OddMath.Diagrams.OddNilHecke.DifferentialComparison
import OddMath.Frontier.ZeroHecke

/-!
# Ellis–Qi Lemmas 3.4 and 3.5 in odd-lean's presented odd nilHecke ring

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §3.2, Lemmas 3.4 and 3.5.

For the dg structure `dONH n` on `NilHeckeAction.Presented n` (rank `n + 2`):

* `dONH_DElem` (**Lemma 3.4**, (3.13)): for the longest divided difference
  `ZeroHecke.DElem n = ∂_0 (∂_1 ∂_0) ⋯ (∂_n ⋯ ∂_0)` (this is exactly Ellis–Qi's choice
  `∂_{w_0} = ∂_1(∂_2∂_1)⋯(∂_{n-1}⋯∂_1)` of (2.39), 0-indexed),
  `d(∂_{w_0}) = Σ_i {i} x_i ∂_{w_0} - (-1)^{binom(n+2,2)} Σ_i {n+1-i} ∂_{w_0} x_i`;
* `dONH_eqIdempotent` (**Lemma 3.5**, (3.16)): for Ellis–Qi's element
  `e = (-1)^{binom(n+2,3)} ∂_{w_0} x^δ` (`eqIdempotent n`, with `x^δ = ZeroHecke.staircaseElem n`),
  `d(e) = Σ_i {i} x_i e`.

Here `{m} = m mod 2`, and indices are 0-based (Ellis–Qi's `x_{i+1}`, `{i}` = their
`{(i+1)-1}`, `{n+1-i}` = their `{(n+2)-(i+1)}`). Ellis–Qi's `e` is the reflection of EKL's
idempotent `(-1)^{binom(n+2,3)} x^δ D` (`ZeroHecke.projector`); idempotence of `e` is not
reproved here.
-/

noncomputable section

namespace OddMath.Diagrams.OddNilHecke

open CategoryTheory StringDiagrams
open OddMath.Frontier NilHeckeAction NilCoxeterWords

theorem presentedEquivEnd_product (n : ℕ) (w : Word n) :
    presentedEquivEnd n (product w) = ψw ℤ (n + 2) (w.map Fin.val) := by
  induction w with
  | nil => rw [product, map_one, List.map_nil, ψw_nil]
  | cons i w ih => rw [product, map_mul, presentedEquivEnd_crossing, ih, List.map_cons, ψw_cons]

theorem presentedEquivEnd_DElem (n : ℕ) :
    presentedEquivEnd n (ZeroHecke.DElem n) = longest ℤ (n + 2) (n + 2) := by
  rw [ZeroHecke.DElem, presentedEquivEnd_product, LongestDivided.wordIn_values, longest]

theorem presentedEquivEnd_staircaseElem (n : ℕ) :
    presentedEquivEnd n (ZeroHecke.staircaseElem n) = staircase ℤ (n + 2) (n + 2) := by
  rw [ZeroHecke.staircaseElem, NilHeckeBasis.dotMonomial, map_list_prod, List.map_map, staircase,
    dotMono, ← List.map_coe_finRange, List.map_map]
  congr 2
  funext i
  simp only [Function.comp_apply, map_pow, presentedEquivEnd_dot]
  congr 1

/-- Integer scalars in the diagrammatic endomorphism ring are multiplication by casts. -/
theorem zsmul_eq_intCast_mul {n : ℕ} (c : ℤ) (f : End ((pres ℤ).obj (strands n))) :
    c • f = (c : End ((pres ℤ).obj (strands n))) * f := by
  rw [Algebra.smul_def, eq_intCast]

/-- **Ellis–Qi, Lemma 3.4** in `Presented n`. -/
theorem dONH_DElem (n : ℕ) :
    dONH n (ZeroHecke.DElem n) =
      ∑ i : Fin (n + 2), ((i.val % 2 : ℕ) : Presented n) * (dot n i * ZeroHecke.DElem n) -
        (-1 : Presented n) ^ (n + 2).choose 2 *
          ∑ i : Fin (n + 2),
            (((n + 1 - i.val) % 2 : ℕ) : Presented n) * (ZeroHecke.DElem n * dot n i) := by
  rw [dONH_eq_iff, presentedEquivEnd_DElem, d_longest ℤ (n + 2) le_rfl, map_sub, map_mul, map_pow,
    map_neg, map_one, map_sum, map_sum]
  simp only [map_mul, map_natCast, presentedEquivEnd_dot, presentedEquivEnd_DElem]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i % 2 : ℕ) : End ((pres ℤ).obj (strands (n + 2)))) *
      (x ℤ (n + 2) i * longest ℤ (n + 2) (n + 2))),
    Fin.sum_univ_eq_sum_range (fun i => (((n + 1 - i) % 2 : ℕ) : End ((pres ℤ).obj (strands (n + 2)))) *
      (longest ℤ (n + 2) (n + 2) * x ℤ (n + 2) i)),
    zsmul_eq_intCast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one]
  simp only [zsmul_eq_intCast_mul, Int.cast_natCast, show n + 2 - 1 = n + 1 by omega]

/-- Ellis–Qi's idempotent `e_{n+2} = (-1)^{binom(n+2,3)} ∂_{w_0} x^δ` (Ellis–Qi, Lemma 2.17 (4);
EKL's `ZeroHecke.projector` is the reflected element `(-1)^{binom(n+2,3)} x^δ ∂_{w_0}`). -/
def eqIdempotent (n : ℕ) : Presented n :=
  (-1 : Presented n) ^ (n + 2).choose 3 * (ZeroHecke.DElem n * ZeroHecke.staircaseElem n)

theorem presentedEquivEnd_eqIdempotent (n : ℕ) :
    presentedEquivEnd n (eqIdempotent n) = idem ℤ (n + 2) (n + 2) := by
  rw [eqIdempotent, map_mul, map_pow, map_neg, map_one, map_mul, presentedEquivEnd_DElem,
    presentedEquivEnd_staircaseElem, idem, zsmul_eq_intCast_mul, Int.cast_pow, Int.cast_neg,
    Int.cast_one]

/-- **Ellis–Qi, Lemma 3.5** in `Presented n`: `d(e) = Σ_i {i} x_i e`. -/
theorem dONH_eqIdempotent (n : ℕ) :
    dONH n (eqIdempotent n) =
      ∑ i : Fin (n + 2), ((i.val % 2 : ℕ) : Presented n) * (dot n i * eqIdempotent n) := by
  rw [dONH_eq_iff, presentedEquivEnd_eqIdempotent, d_idem ℤ (n + 2) le_rfl, map_sum]
  simp only [map_mul, map_natCast, presentedEquivEnd_dot, presentedEquivEnd_eqIdempotent]
  rw [Fin.sum_univ_eq_sum_range (fun i => ((i % 2 : ℕ) : End ((pres ℤ).obj (strands (n + 2)))) *
      (x ℤ (n + 2) i * idem ℤ (n + 2) (n + 2)))]
  simp only [zsmul_eq_intCast_mul, Int.cast_natCast]

end OddMath.Diagrams.OddNilHecke

end

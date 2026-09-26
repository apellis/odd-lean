import OddMath.Frontier.OddLRRuleExample
import OddMath.Frontier.OddLRHive

/-!
# Misprints in [E], §4.2 and (4.18)

Source: A. P. Ellis, *The odd Littlewood–Richardson rule*, arXiv:1111.3932v1.

* **§4.2, p. 13.** The display `sign(S) = sign(Ŝ) = N^<(Ŝ)` should read
  `sign(S) = sign(Ŝ) = (−1)^{N^<(Ŝ)}` (`OddLRTableau.SkewTableau.sign`). For the two
  Littlewood–Richardson tableaux of Example 4.9, `N^< = 7` and `N^< = 6`, while the signs are
  `−1` and `1` (`sign_display_printed_false`); the printed value `6` is not a sign
  (`printed_value_not_sign`).
* **(4.18), p. 19.** In `Q_𝔥(H) = Σ_{i=1}^{n} Σ_{j=i}^{n} h_{i−1,j−1}(h_{i,j} − h_{i−1,j} − h_{i,j−1}
  + h_{i−1,j−1}) − Σ_{i=1}^{n−1} h_{i,i}²`, the right-slanted rhombus inequality (R) makes the
  parenthesized term non-negative for `j > i` (`eq_4_18_term_nonneg`), but not for `j = i`: the
  hive `hexH` with `n = 2` has term `−1` at `i = j = 1` (`eq_4_18_diagonal_term_neg`).
-/

namespace OddMath.Frontier.ErrataChecks
open OddLRTableau OddLRRule OddLRHive

/-! ## The sign of a skew tableau, §4.2 -/

/-- [E] §4.2, p. 13: the printed `sign(S) = N^<(Ŝ)` fails for both LR tableaux of Example 4.9:
`N^< = 7` with sign `−1`, and `N^< = 6` with sign `1`. -/
theorem sign_display_printed_false :
    exS1.Nlt = 7 ∧ exS1.sign = -1 ∧ exS1.sign ≠ (exS1.Nlt : ℤ) ∧
    exS2.Nlt = 6 ∧ exS2.sign = 1 ∧ exS2.sign ≠ (exS2.Nlt : ℤ) := by
  unfold SkewTableau.sign
  rw [Nlt_exS1, Nlt_exS2]
  norm_num

/-- [E] §4.2, p. 13: the printed value `N^<(Ŝ)` is not a sign: `N^< = 6 ∉ {1, −1}` for the second
tableau of Example 4.9. -/
theorem printed_value_not_sign : (exS2.Nlt : ℤ) ≠ 1 ∧ (exS2.Nlt : ℤ) ≠ -1 := by
  rw [Nlt_exS2]; norm_num

/-! ## (4.18), p. 19 -/

/-- The parenthesized term of (4.18): `h_{i,j} − h_{i−1,j} − h_{i,j−1} + h_{i−1,j−1}`, with the
convention `h_{i,j} = 0` outside `0 ≤ i ≤ j ≤ n`. -/
def rhombusTerm {n : ℕ} (H : V ℤ n) (i j : ℕ) : ℤ :=
  coord H i j - coord H (i-1) j - coord H i (j-1) + coord H (i-1) (j-1)

/-- [E] (4.18): for `1 ≤ i < j ≤ n` the term is non-negative, by (R). -/
theorem eq_4_18_term_nonneg {n : ℕ} {H : V ℤ n} (hH : IsHive H) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hj : j ≤ n) : 0 ≤ rhombusTerm H i j := by
  have := hH.R i j hi hij hj
  unfold rhombusTerm
  linarith

/-- Values of a hive with `n = 2`: `h_{0,0} = h_{0,1} = h_{0,2} = 0`, `h_{1,1} = h_{1,2} = −1`,
`h_{2,2} = −2`. -/
def hexF : ℕ → ℕ → ℤ
  | 1, 1 => -1
  | 1, 2 => -1
  | 2, 2 => -2
  | _, _ => 0

/-- The hive `hexH`. -/
def hexH : V ℤ 2 := fun x => hexF x.i x.j

theorem coord_hexH (i j : ℕ) : coord hexH i j = if i ≤ j ∧ j ≤ 2 then hexF i j else 0 := by
  unfold coord
  split_ifs <;> rfl

/-- `hexH` satisfies (4.15) (R), (V), (L), each of which is non-vacuous for `n = 2`. -/
theorem hexH_isHive : IsHive hexH := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coord_hexH]; rfl
  · intro i j hi hij hj
    obtain rfl : j = 2 := by omega
    obtain rfl : i = 1 := by omega
    simp [coord_hexH, hexF]
  · intro i j hi hij hj
    obtain rfl : j = 1 := by omega
    obtain rfl : i = 1 := by omega
    simp [coord_hexH, hexF]
  · intro i j hi hij hj
    obtain rfl : j = 1 := by omega
    obtain rfl : i = 1 := by omega
    simp [coord_hexH, hexF]

/-- [E] (4.18): for `j = i` the parenthesized term is not controlled by (R); for the hive `hexH`
it equals `−1` at `i = j = 1`. -/
theorem eq_4_18_diagonal_term_neg : IsHive hexH ∧ rhombusTerm hexH 1 1 = -1 := by
  refine ⟨hexH_isHive, ?_⟩
  simp [rhombusTerm, coord_hexH, hexF]

end OddMath.Frontier.ErrataChecks

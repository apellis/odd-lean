import OddMath.Diagrams.OddNilHecke.DifferentialLongestComparison
import OddMath.Frontier.ThickBubble
import OddMath.Frontier.ShuffleLemma
import OddMath.Frontier.LongestFactor
import OddMath.Frontier.EKLSectionTwoE
import OddMath.Frontier.OnhReflection
import OddMath.Frontier.ProjectorRank

/-!
# Ellis–Qi thick calculus: the idempotents `e_n` and their blocks

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*,
arXiv:1504.01712v2, §4.1 and §4.2.1.

Ellis–Qi use the idempotent `e_n = (-1)^{C(n,3)} ∂_{w_0} x^δ` (`eqIdempotent`, Lemma 2.17 (4)),
the reflection about a horizontal axis of EKL's `(-1)^{C(n,3)} x^δ ∂_{w_0}` (Remark 4.1).
Rank is `m + 2`, strands and dots are `0`-indexed, and a written product `x * y` is `x` drawn on
top of `y`.  In the faithful polynomial representation on `OPol = SkewPolynomial (m+2)`:

* `e_n` acts by `f ↦ (-1)^{C(n,3)} ∂_{w_0}(x^δ f)` (`action_eqIdempotent`), is the identity on the
  joint kernel `OΛ` of the `∂_i` and maps into it; hence `e_n² = e_n` and `e_n ∂_{w_0} = ∂_{w_0}`;
* `∂_{w_0}(x^δ x_j) = 0` for `j ≥ 1` (the monomial has equal adjacent exponents), so
  `e_n x_j ∂_{w_0} = 0` and `e_n x_j e_n = 0` for `j ≥ 1`; this is the vanishing used in §4.2.1;
* `e_n x_1 e_n = ẽ_1 e_n` for the twisted elementary polynomial
  `ẽ_1 = x_1 - x_2 + x_3 - ⋯` (`etElem`; §4.1, the "convenient relation" for `k = 1`),
  `e_n ẽ_1 e_n = ẽ_1 e_n`, and `ẽ_1 ∂_{w_0} = (-1)^{C(n-1,2)} ∂_{w_0} ẽ_1`.

The same objects on a window of strands `[p, p+k)` of rank `n + 2` (`eqBlock`, `etBlock`) are
the images under `OnhWindow.windowHom` for `k ≥ 2` and `1`, `x_p` for `k = 1`; the window
statements are transported through `action_windowHom_place`.
-/

namespace OddMath.Frontier.EQThick

open OddMath.SkewPolynomial (SkewPolynomial generator monomial)
open NilHeckeAction NilCoxeterWords NilHeckeBasis ZeroHecke OnhWindow ThickBubble
open OddMath.Diagrams.OddNilHecke (dONH eqIdempotent parity dONH_mul dot_mem_parity
  crossing_mem_parity one_mem_parity mul_mem_parity)
open FiniteCompleteElementary
open scoped BigOperators

noncomputable section

/-- The joint kernel `OΛ` of the odd divided differences. -/
abbrev K (m : ℕ) := OddSymmetricKernel.kernelSubring m

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : ℤ) ^ k * (-1 : ℤ) ^ k = 1 := by
  rw [← mul_pow]; norm_num

/-! ## The idempotent `e_n` in rank `m + 2` -/

section Rank
variable {m : ℕ}

theorem eqIdempotent_eq_zsmul (m : ℕ) :
    eqIdempotent m = (-1 : ℤ) ^ (m + 2).choose 3 • (DElem m * staircaseElem m) := by
  rw [OddMath.Diagrams.OddNilHecke.eqIdempotent, zsmul_eq_mul]
  simp only [Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- `e_n` acts by `f ↦ (-1)^{C(n,3)} ∂_{w_0}(x^δ f)`. -/
theorem action_eqIdempotent (f : SkewPolynomial (m + 2)) :
    action m (eqIdempotent m) f =
      (-1 : ℤ) ^ (m + 2).choose 3 • LongestDivided.D (m + 2) (LongestDivided.staircase (m + 2) * f) := by
  rw [eqIdempotent_eq_zsmul, map_zsmul, LinearMap.smul_apply, action_mul_apply,
    ZeroHecke.action_DElem, action_staircaseElem_apply]

/-- `e_n` is the identity on `OΛ`. -/
theorem action_eqIdempotent_kernel {h : SkewPolynomial (m + 2)} (hh : h ∈ K m) :
    action m (eqIdempotent m) h = h := by
  rw [action_eqIdempotent, LongestDivided.D_right_kernel m _ _ hh, LongestDivided.D_staircase,
    smul_mul_assoc, one_mul, smul_smul, neg_one_pow_mul_self, one_smul]

/-- `e_n` maps into `OΛ`. -/
theorem action_eqIdempotent_mem (f : SkewPolynomial (m + 2)) :
    action m (eqIdempotent m) f ∈ K m := by
  rw [action_eqIdempotent]
  exact Subring.zsmul_mem _ (LongestKernel.D_mem_kernel m _) _

theorem action_eqIdempotent_one : action m (eqIdempotent m) 1 = 1 :=
  action_eqIdempotent_kernel (Subring.one_mem _)

/-- `e_n² = e_n`. -/
theorem eqIdempotent_mul_self (m : ℕ) : eqIdempotent m * eqIdempotent m = eqIdempotent m := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_eqIdempotent_kernel (action_eqIdempotent_mem f)]

/-- `e_n ∂_{w_0} = ∂_{w_0}`. -/
theorem eqIdempotent_mul_DElem (m : ℕ) : eqIdempotent m * DElem m = DElem m := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, ZeroHecke.action_DElem,
    action_eqIdempotent_kernel (LongestKernel.D_mem_kernel m f)]

/-- `∂_{w_0}(x^δ x_j) = 0` for `j ≥ 1`: the exponents of `x_{j-1}` and `x_j` agree. -/
theorem D_staircase_mul_generator {j : Fin (m + 2)} (hj : 1 ≤ j.val) :
    LongestDivided.D (m + 2) (LongestDivided.staircase (m + 2) * generator j) = 0 := by
  obtain ⟨L, ε, -, hD⟩ := LongestFactor.D_factor_first m ⟨j.val - 1, by omega⟩
  rw [hD, LinearMap.smul_apply, LinearMap.comp_apply, LongestDivided.staircase,
    OddMath.SkewPolynomial.generator, MonomialReversal.monomial_mul_monomial,
    ShuffleLemma.divided_monomial_balanced, map_zero, smul_zero]
  simp only [Pi.add_apply, OddMath.SkewPolynomial.expSingle, Fin.castSucc_mk, Fin.succ_mk,
    Fin.ext_iff]
  split_ifs <;> omega

/-- The twisted elementary polynomial `ẽ_1 = Σ_j (-1)^j x_j` as an element of `ONH`. -/
def etElem (m : ℕ) : Presented m := ∑ j : Fin (m + 2), (-1 : ℤ) ^ j.val • dot m j

theorem polyElem_elementary_one (m : ℕ) :
    OnhPolynomial.polyElem m (elementaryPoly (m + 2) 1) = etElem m := by
  rw [EKLSectionTwo.elementary_one_eq, map_sum, etElem]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [PlacticEvaluation.tildeGenerator, map_zsmul, OnhPolynomial.polyElem_generator]

theorem action_etElem (f : SkewPolynomial (m + 2)) :
    action m (etElem m) f = elementaryPoly (m + 2) 1 * f := by
  rw [← polyElem_elementary_one, OnhPolynomial.action_polyElem]

theorem action_eqIdempotent_generator {j : Fin (m + 2)} (hj : 1 ≤ j.val) :
    action m (eqIdempotent m) (generator j) = 0 := by
  rw [action_eqIdempotent, D_staircase_mul_generator hj, smul_zero]

/-- `e_n(x_0) = ẽ_1`. -/
theorem action_eqIdempotent_generator_zero :
    action m (eqIdempotent m) (generator 0) = elementaryPoly (m + 2) 1 := by
  have hsum : action m (eqIdempotent m) (elementaryPoly (m + 2) 1) =
      action m (eqIdempotent m) (generator 0) := by
    rw [EKLSectionTwo.elementary_one_eq, map_sum, Fin.sum_univ_succ,
      Finset.sum_eq_zero fun j _ => by
        rw [PlacticEvaluation.tildeGenerator, map_zsmul,
          action_eqIdempotent_generator (by simp), smul_zero],
      add_zero, PlacticEvaluation.tildeGenerator, Fin.val_zero, pow_zero, one_smul]
  rw [← hsum, action_eqIdempotent_kernel (OddSymmetricKernel.elementary_mem m 1)]

/-- `e_n x_j ∂_{w_0} = 0` for `j ≥ 1`. -/
theorem eqIdempotent_dot_DElem {j : Fin (m + 2)} (hj : 1 ≤ j.val) :
    eqIdempotent m * dot m j * DElem m = 0 := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_mul_apply, action_dot_apply, ZeroHecke.action_DElem,
    NilHeckeRightKernel.action_right_mul m _ _ (LongestKernel.D_mem_kernel m f),
    action_eqIdempotent_generator hj, map_zero, LinearMap.zero_apply]
  exact OddMath.SkewPolynomial.zero_mul _

/-- `e_n x_j e_n = 0` for `j ≥ 1`. -/
theorem eqIdempotent_dot_eqIdempotent {j : Fin (m + 2)} (hj : 1 ≤ j.val) :
    eqIdempotent m * dot m j * eqIdempotent m = 0 := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_mul_apply, action_dot_apply,
    NilHeckeRightKernel.action_right_mul m _ _ (action_eqIdempotent_mem f),
    action_eqIdempotent_generator hj, map_zero, LinearMap.zero_apply]
  exact OddMath.SkewPolynomial.zero_mul _

/-- Ellis–Qi §4.1, the relation `e_n x_1 e_n = ẽ_1 e_n` (`k = 1`, `0`-indexed dot `x_0`). -/
theorem eqIdempotent_dot_zero_eqIdempotent :
    eqIdempotent m * dot m 0 * eqIdempotent m = etElem m * eqIdempotent m := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_mul_apply, action_dot_apply,
    NilHeckeRightKernel.action_right_mul m _ _ (action_eqIdempotent_mem f),
    action_eqIdempotent_generator_zero, action_mul_apply, action_etElem]

/-- `e_n ẽ_1 e_n = ẽ_1 e_n`. -/
theorem eqIdempotent_etElem_eqIdempotent :
    eqIdempotent m * etElem m * eqIdempotent m = etElem m * eqIdempotent m := by
  apply NilHeckeBasis.action_injective m
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, action_mul_apply, action_etElem, action_eqIdempotent_kernel
    (Subring.mul_mem _ (OddSymmetricKernel.elementary_mem m 1) (action_eqIdempotent_mem f)),
    action_mul_apply, action_etElem]

/-- `ẽ_1 ∂_{w_0} = (-1)^{C(n-1,2)} ∂_{w_0} ẽ_1` (EKL (2.64) and EKL Lemma 2.16). -/
theorem etElem_mul_DElem (m : ℕ) :
    etElem m * DElem m = (-1 : ℤ) ^ (m + 1).choose 2 • (DElem m * etElem m) := by
  have h := OnhPolynomial.DElem_poly_kernel (elementaryPoly (m + 2) 1)
    (OddSymmetricKernel.elementary_mem m 1)
  rw [LongestElementary.action_elementary, map_zsmul, polyElem_elementary_one,
    smul_mul_assoc] at h
  rw [h, smul_smul, show (m + 2 - 1) = m + 1 by omega, show Nat.choose 1 2 = 0 by rfl, zero_add,
    one_mul, neg_one_pow_mul_self, one_smul]

end Rank

/-! ## Windows -/

section Window
variable {n : ℕ}

/-- A windowed element acts on placed polynomials through the original action. -/
theorem action_windowHom_place {m p : ℕ} (h : p + (m + 2) ≤ n + 2) (y : Presented m)
    (f : SkewPolynomial (m + 2)) :
    action n (windowHom m n p h y) (ProjectorRank.place p h f) =
      ProjectorRank.place p h (action m y f) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction a using FreeAlgebra.induction generalizing f with
  | grade0 r =>
    simp only [algebraMap_int_eq, eq_intCast, map_intCast, Module.End.intCast_apply, map_zsmul]
  | grade1 g =>
    cases g with
    | inl j =>
      change action n (windowHom m n p h (dot m j)) _ = ProjectorRank.place p h (action m (dot m j) f)
      rw [windowHom_dot, action_dot_apply, action_dot_apply, map_mul, ProjectorRank.place_generator]
      rfl
    | inr i =>
      change action n (windowHom m n p h (crossing m i)) _ =
        ProjectorRank.place p h (action m (crossing m i) f)
      rw [windowHom_crossing, action_crossing_apply, action_crossing_apply]
      exact (ProjectorRank.place_divided_and_s h i f).1
  | add a b ha hb =>
    simp only [map_add, LinearMap.add_apply, ha, hb]
  | mul a b ha hb =>
    rw [(Ideal.Quotient.mk _).map_mul, (windowHom _ _ _ _).map_mul, action_mul_apply, hb, ha,
      action_mul_apply]

/-- Ellis–Qi's idempotent `e_k` on the strands `[p, p+k)`:
`(-1)^{C(k,3)} ∂_{w_0} x^δ` with `∂_{w_0} = blockD` and `x^δ = x_p^{k-1} ⋯ x_{p+k-2}`. -/
def eqBlock (n p k : ℕ) (h : p + k ≤ n + 2) : Presented n :=
  (-1 : ℤ) ^ k.choose 3 • (blockD n p k * blockMono n p k h fun i => k - 1 - i.val)

/-- The twisted elementary polynomial `ẽ_1 = x_p - x_{p+1} + ⋯ ± x_{p+k-1}` on the strands
`[p, p+k)` (Ellis–Qi, text after Proposition 4.2). -/
def etBlock (n p k : ℕ) (h : p + k ≤ n + 2) : Presented n :=
  ∑ i : Fin k, (-1 : ℤ) ^ i.val • dot n (shiftFin h i)

theorem eqBlock_eq {m p : ℕ} (h : p + (m + 2) ≤ n + 2) :
    eqBlock n p (m + 2) h = windowHom m n p h (eqIdempotent m) := by
  rw [eqBlock, eqIdempotent_eq_zsmul, map_zsmul, map_mul, ← blockD_eq h, ← blockMono_eq h]
  congr 3

theorem eqBlock_zero (p : ℕ) (h : p + 0 ≤ n + 2) : eqBlock n p 0 h = 1 := by
  simp [eqBlock, blockD_zero, blockMono]

theorem eqBlock_one (p : ℕ) (h : p + 1 ≤ n + 2) : eqBlock n p 1 h = 1 := by
  simp [eqBlock, blockD_one, blockMono, show Nat.choose 1 3 = 0 by rfl]

theorem etBlock_eq {m p : ℕ} (h : p + (m + 2) ≤ n + 2) :
    etBlock n p (m + 2) h = windowHom m n p h (etElem m) := by
  rw [etBlock, etElem, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, windowHom_dot]
  rfl

theorem etBlock_one (p : ℕ) (h : p + 1 ≤ n + 2) :
    etBlock n p 1 h = dot n ⟨p, by omega⟩ := by
  simp [etBlock, shiftFin]

theorem homog_eqBlock {p k : ℕ} (h : p + k ≤ n + 2) :
    Homog p (p + k) (2 * k.choose 2) (eqBlock n p k h) := by
  refine Homog.zsmul (homog_of_eq ((homog_blockD h).mul (homog_blockMono h _)) ?_) _
  rw [StaircaseValley.sum_staircase]
  ring

theorem homog_etBlock {p k : ℕ} (h : p + k ≤ n + 2) : Homog p (p + k) 1 (etBlock n p k h) := by
  rw [etBlock]
  induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact Homog.zero 1
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (Homog.zsmul (Homog.gen (IsGen.dot _ (by simp [shiftFin])
      (by have := i.isLt; simp [shiftFin]; omega))) _).add ih

/-- Products of `k` generators have parity `k`. -/
theorem _root_.OddMath.Frontier.OnhWindow.Homog.mem_parity {l r k : ℕ} {u : Presented n} (hu : Homog l r k u) :
    u ∈ parity n (k : ZMod 2) := by
  induction hu with
  | one => simpa using one_mem_parity n
  | gen hx =>
    cases hx with
    | dot j _ _ => simpa using dot_mem_parity n j
    | crossing i _ _ => simpa using crossing_mem_parity n i
  | mul _ _ hx hy => simpa [Nat.cast_add] using mul_mem_parity hx hy
  | zero k => exact zero_mem _
  | add _ _ hx hy => exact add_mem hx hy
  | neg _ hx => exact neg_mem hx

theorem eqBlock_mem_parity {p k : ℕ} (h : p + k ≤ n + 2) : eqBlock n p k h ∈ parity n 0 := by
  have := (homog_eqBlock h).mem_parity
  rwa [Nat.cast_mul, show ((2 : ℕ) : ZMod 2) = 0 from rfl, zero_mul] at this

theorem eqBlock_mul_self {p k : ℕ} (h : p + k ≤ n + 2) :
    eqBlock n p k h * eqBlock n p k h = eqBlock n p k h := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, mul_one]
  | h1 => rw [eqBlock_one, mul_one]
  | h2 m => rw [eqBlock_eq h, ← map_mul, eqIdempotent_mul_self]

theorem action_eqBlock_one {p k : ℕ} (h : p + k ≤ n + 2) : action n (eqBlock n p k h) 1 = 1 := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, map_one (action n)]; rfl
  | h1 => rw [eqBlock_one, map_one (action n)]; rfl
  | h2 m =>
    rw [eqBlock_eq h, ← map_one (ProjectorRank.place p h), action_windowHom_place,
      action_eqIdempotent_one]

/-- A block idempotent is absorbed by the full idempotent: `e_k^{[p,p+k)} e_n = e_n`. -/
theorem eqBlock_mul_eqIdempotent {p k : ℕ} (h : p + k ≤ n + 2) :
    eqBlock n p k h * eqIdempotent n = eqIdempotent n := by
  apply NilHeckeBasis.action_injective n
  apply LinearMap.ext
  intro f
  rw [action_mul_apply, ← one_mul (action n (eqIdempotent n) f),
    NilHeckeRightKernel.action_right_mul n _ _ (action_eqIdempotent_mem f), action_eqBlock_one]

theorem place_generator_eq {m p : ℕ} (h : p + (m + 2) ≤ n + 2) (j : Fin (m + 2)) :
    ProjectorRank.place p h (generator j) = generator ⟨j.val + p, by omega⟩ :=
  ProjectorRank.place_generator p h j

/-- `e_k(x_{p+i}) = 0` on the window for `1 ≤ i < k`. -/
theorem action_eqBlock_generator {p k : ℕ} (h : p + k ≤ n + 2) (i : ℕ) (hi1 : 1 ≤ i)
    (hik : i < k) : action n (eqBlock n p k h) (generator ⟨p + i, by omega⟩) = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
  have hg : generator (⟨p + i, by omega⟩ : Fin (n + 2)) =
      ProjectorRank.place p h (generator ⟨i, hik⟩) := by
    rw [place_generator_eq]; congr 1; ext; simp; omega
  rw [eqBlock_eq h, hg, action_windowHom_place, action_eqIdempotent_generator hi1, map_zero]

/-- `e_k(x_p) = ẽ_1` on the window. -/
theorem action_eqBlock_generator_self {p k : ℕ} (h : p + k ≤ n + 2) (hk : 1 ≤ k) :
    action n (eqBlock n p k h) (generator ⟨p, by omega⟩) = action n (etBlock n p k h) 1 := by
  obtain rfl | ⟨m, rfl⟩ : k = 1 ∨ ∃ m, k = m + 2 :=
    if hk1 : k = 1 then Or.inl hk1 else Or.inr ⟨k - 2, by omega⟩
  · rw [eqBlock_one, etBlock_one, map_one (action n), action_dot_apply]; exact (mul_one _).symm
  · have hg : generator (⟨p, by omega⟩ : Fin (n + 2)) = ProjectorRank.place p h (generator 0) := by
      rw [place_generator_eq]; congr 1; ext; simp
    rw [eqBlock_eq h, etBlock_eq h, hg, action_windowHom_place, action_eqIdempotent_generator_zero,
      ← map_one (ProjectorRank.place p h), action_windowHom_place, action_etElem, mul_one]

/-- `e_k(ẽ_1) = ẽ_1` on the window. -/
theorem action_eqBlock_etBlock {p k : ℕ} (h : p + k ≤ n + 2) :
    action n (eqBlock n p k h) (action n (etBlock n p k h) 1) = action n (etBlock n p k h) 1 := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, map_one (action n)]; rfl
  | h1 => rw [eqBlock_one, map_one (action n)]; rfl
  | h2 m =>
    rw [eqBlock_eq h, etBlock_eq h, ← map_one (ProjectorRank.place p h), action_windowHom_place,
      action_windowHom_place, action_etElem, mul_one,
      action_eqIdempotent_kernel (OddSymmetricKernel.elementary_mem m 1)]

/-- `e_k ẽ_1 e_k = ẽ_1 e_k` on the window. -/
theorem eqBlock_etBlock_eqBlock {p k : ℕ} (h : p + k ≤ n + 2) :
    eqBlock n p k h * etBlock n p k h * eqBlock n p k h = etBlock n p k h * eqBlock n p k h := by
  induction k using block_cases with
  | h0 => rw [eqBlock_zero, mul_one, one_mul, mul_one]
  | h1 => rw [eqBlock_one, mul_one, one_mul, mul_one]
  | h2 m => rw [eqBlock_eq h, etBlock_eq h, ← map_mul, ← map_mul, ← map_mul,
      eqIdempotent_etElem_eqIdempotent]

/-- `ẽ_1 ∂_{w_0} = (-1)^{C(k-1,2)} ∂_{w_0} ẽ_1` on the window. -/
theorem etBlock_mul_blockD {p k : ℕ} (h : p + k ≤ n + 2) :
    etBlock n p k h * blockD n p k = (-1 : ℤ) ^ (k - 1).choose 2 • (blockD n p k * etBlock n p k h) := by
  induction k using block_cases with
  | h0 => simp [blockD_zero]
  | h1 => simp [blockD_one]
  | h2 m =>
    rw [etBlock_eq h, blockD_eq h, ← map_mul, etElem_mul_DElem, map_zsmul, map_mul,
      show m + 2 - 1 = m + 1 by omega]

end Window

end

end OddMath.Frontier.EQThick

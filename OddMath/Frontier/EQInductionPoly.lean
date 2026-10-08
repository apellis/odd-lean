import OddMath.Frontier.EQFunctorRingTensor
import OddMath.Frontier.EQSchurDifferential

/-!
# Block twists of `OPol_{a+b}`

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.3 (Definition 4.6) and §4.4 (Corollary 4.21). Auxiliary ring endomorphisms of
`OPol_{a+b} = OPol_a ⊠ OPol_b` (variables `x_1, …, x_a`, `y_1, …, y_b`) used to compare
`(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z_{a,b}` with `Z_{a+b}`:

* `blockRev a b`: the plain permutation `w₀ × w₀ ∈ S_a × S_b` (reversal inside each block), with
  `blockRev (f(x) g(y)) = (w₀ f)(x) (w₀ g)(y)`;
* the twisted Leibniz rule for `θ_a ⊗ θ_b` (`EQZab.tauAB`):
  `d(θ_{ab} f) = θ_{ab}(d f) + s_β θ_{ab}(f) - ι(θ_{ab} f) s_β` with `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`
  (`d_tauAB`);
* `sAlpha_zAlpha_eq`: `s_{(0,1,0,…)}` in `a + b` variables is `s_β + {a} θ_b(e_1)(y)`.
-/

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY diagHom diagHom_generator inclX_generator inclY_generator
  par tauAB tauCoeff parityInv_tauAB)

noncomputable section

variable (a b : ℕ)

/-! ## The block reversal `w₀ × w₀` -/

/-- The permutation of `Fin (a + b)` reversing each of the blocks `[0, a)` and `[a, a + b)`. -/
def blockRevPerm : Equiv.Perm (Fin (a + b)) :=
  finSumFinEquiv.symm.trans ((Equiv.sumCongr Fin.revPerm Fin.revPerm).trans finSumFinEquiv)

theorem blockRevPerm_castAdd (i : Fin a) :
    blockRevPerm a b (Fin.castAdd b i) = Fin.castAdd b i.rev := by
  simp [blockRevPerm]

theorem blockRevPerm_natAdd (j : Fin b) :
    blockRevPerm a b (Fin.natAdd a j) = Fin.natAdd a j.rev := by
  simp [blockRevPerm]

/-- `w₀ × w₀`, the plain permutation reversing the variables `x` and the variables `y`. -/
def blockRev : SkewPolynomial (a + b) →+* SkewPolynomial (a + b) :=
  skewLift (fun j => (1 : ℤ) • generator (blockRevPerm a b j))
    (fun i j h => smul_generator_anticomm (fun _ => 1) (blockRevPerm a b) i j h)

variable {a b}

theorem blockRev_generator (j : Fin (a + b)) :
    blockRev a b (generator j) = generator (blockRevPerm a b j) := by
  simp [blockRev]

theorem blockRev_inclX (f : SkewPolynomial a) :
    blockRev a b (inclX a b f) = inclX a b (longestPerm a f) := by
  have h : (blockRev a b).comp (inclX a b) = (inclX a b).comp (longestPerm a) :=
    ringHom_ext fun i => by
      simp [blockRev_generator, blockRevPerm_castAdd]
  exact RingHom.congr_fun h f

theorem blockRev_inclY (f : SkewPolynomial b) :
    blockRev a b (inclY a b f) = inclY a b (longestPerm b f) := by
  have h : (blockRev a b).comp (inclY a b) = (inclY a b).comp (longestPerm b) :=
    ringHom_ext fun j => by
      simp [blockRev_generator, blockRevPerm_natAdd]
  exact RingHom.congr_fun h f

/-! ## The twisted Leibniz rule for `θ_a ⊗ θ_b` -/

theorem tauAB_generator (i : Fin (a + b)) : tauAB a b (generator i) = tauCoeff a b i • generator i := by
  simp [tauAB]

variable (a b) in
/-- `β = (0,1,0,1,…) ⊔ (0,1,0,1,…)`: the pattern `zAlpha` on each block. -/
def zAB (i : Fin (a + b)) : ℤ := if i.val < a then ((i.val % 2 : ℕ) : ℤ) else (((i.val - a) % 2 : ℕ) : ℤ)

theorem tauCoeff_identity (i : Fin (a + b)) :
    tauCoeff a b i = tauCoeff a b i * tauCoeff a b i + tauCoeff a b i * (2 * zAB a b i) := by
  unfold tauCoeff zAB
  split_ifs with h1 h2 h2
  · omega
  · rcases Nat.even_or_odd (i.val - a) with he | ho
    · rw [Nat.even_iff.mp he, he.neg_one_pow]; norm_num
    · rw [Nat.odd_iff.mp ho, ho.neg_one_pow]; norm_num
  · rcases Nat.even_or_odd i.val with he | ho
    · rw [Nat.even_iff.mp he, he.neg_one_pow]; norm_num
    · rw [Nat.odd_iff.mp ho, ho.neg_one_pow]; norm_num
  · omega

/-- `d(θ_{ab} f) = θ_{ab}(d f) + s_β θ_{ab}(f) - ι(θ_{ab} f) s_β` for `θ_{ab} = θ_a ⊗ θ_b`. -/
theorem d_tauAB (f : SkewPolynomial (a + b)) :
    d (a + b) (tauAB a b f) = tauAB a b (d (a + b) f) + sAlpha (zAB a b) * tauAB a b f -
      parityInv (a + b) (tauAB a b f) * sAlpha (zAB a b) := by
  induction f using induction_generator with
  | hgen j =>
    have hs := eq_sub_of_add_eq (sAlpha_mul_generator_add (zAB a b) j)
    have hc := tauCoeff_identity (a := a) (b := b) j
    rw [tauAB_generator, map_zsmul, d_generator, map_mul, tauAB_generator,
      map_zsmul, parityInv_generator, smul_mul_smul_comm, mul_smul_comm, hs, smul_neg, neg_mul,
      smul_mul_assoc]
    set Y := generator j * generator j
    set Z := generator j * sAlpha (zAB a b)
    rw [smul_sub, smul_smul]
    conv_lhs => rw [hc]
    rw [add_smul]
    abel
  | h0 => rw [map_zero, map_zero, map_zero, map_zero, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul,
      sub_zero, add_zero]
  | h1 => simp
  | hadd f g hf hg =>
    rw [map_add, map_add, hf, hg, map_add, map_add, map_add]
    simp only [mul_add, add_mul]
    abel
  | hneg f hf =>
    rw [map_neg, map_neg, hf, map_neg, map_neg, map_neg]
    simp only [mul_neg, neg_mul]
    abel
  | hmul f g hf hg =>
    rw [map_mul, d_mul, d_mul, map_add, map_mul, map_mul, ← parityInv_tauAB, map_mul]
    exact twisted_leibniz_aux _ _ _ _ _ _ _ _ _ hf hg

/-- `s_{(0,1,0,…)} = s_β + {a} θ_b(e_1)(y)` in `a + b` variables. -/
theorem sAlpha_zAlpha_eq :
    sAlpha (zAlpha (a + b)) = sAlpha (zAB a b) + par a • inclY a b (theta b (elementary b 1)) := by
  rw [show theta b (elementary b 1) = ∑ j : Fin b, (-1 : ℤ) ^ j.val • generator j by
    rw [elementary, EQZab.strictSum_one, map_sum]
    simp]
  rw [map_sum, Finset.smul_sum, sAlpha, sAlpha, Fin.sum_univ_add, Fin.sum_univ_add, add_assoc]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    simp [zAlpha, zAB, i.isLt]
  · rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [zAlpha, zAB, Fin.val_natAdd, map_zsmul, inclY_generator, smul_smul, ← add_smul]
    simp only [show ¬(a + j.val < a) by omega, ↓reduceIte, show a + j.val - a = j.val by omega]
    congr 1
    unfold par
    rcases Nat.even_or_odd j.val with hj | hj
    · have hj' := Nat.even_iff.mp hj
      rw [hj.neg_one_pow, hj']
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, show (a + j.val) % 2 = 0 by omega]; norm_num
      · rw [ha, show (a + j.val) % 2 = 1 by omega]; norm_num
    · have hj' := Nat.odd_iff.mp hj
      rw [hj.neg_one_pow, hj']
      rcases Nat.mod_two_eq_zero_or_one a with ha | ha
      · rw [ha, show (a + j.val) % 2 = 1 by omega]; norm_num
      · rw [ha, show (a + j.val) % 2 = 0 by omega]; norm_num

end

end OddMath.Frontier.EQFunctor

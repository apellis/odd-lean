import OddMath.Frontier.EQOnhNat
import OddMath.Frontier.EQInductionFunctor
import OddMath.Frontier.EQZnMorita

/-!
# The restriction half of Ellis–Qi, Corollary 4.21

Source: A. P. Ellis, Y. Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2,
§4.4, Definition 4.15 (`Z^♮_{a,b}`), (4.32), Definition 4.20 and Corollary 4.21; ranks `a + 2`, `b + 2`.

* `swapPoly A B`: `OPol_{A+B} → OPol_{A+B}`, `f(x_1, …, x_{A+B}) ↦ f(y_1, …, y_B, x_1, …, x_A)`; it maps
  `OΛ_{A+B}` into `OΛ_A ⊠ OΛ_B` (`swapPoly_mem`), giving the morphism of dg rings
  `swapDG : OΛ_{a+b} → OΛ_a ⊗ OΛ_b`;
* `ZNat a b`: `Z^♮_{a,b}` of Definition 4.15, the dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule `OΛ_a ⊗ OΛ_b`
  with `OΛ_{a+b}` acting on the right through `swapDG` (`d(1^♮) = 0`, generator in degree `0`);
* `thetaC`, `thetaP`: `Θ : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b} → Z_{a+b}`, `y ⊗ r ↦ (y r)(x, y) P^a`
  with `P = x_{a+1} ⋯ x_{a+b}`: injective onto `P^a Z_{a+b}`, left `ONH_a ⊗ ONH_b`-linear through `ι`,
  right `OΛ_{a+b}`-linear up to the sign `(-1)^{ab |h|}` (`thetaP_op_smul`), of degree `ab`, and
  commuting with `d` (`thetaP_d`);
* **`gEquiv a b`**: `((Z_a ⊠ Z_b) ⊗ Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}` as dg
  `(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodules (`gEquiv_op_smul`), with `ONH^♮_{a+b} = ONHNat a b` the right
  ideal `P^a ONH_{a+b}` regraded so that `P^a` has degree `0`;
* **`resIsoA a b : J^A ⋙ R ≅ Res^♮ ⋙ J^A`** (the restriction half of Corollary 4.21 on abelian
  categories), `resIsoH` (homotopy categories) and `resIsoD` (derived categories, where
  `D(ONH_{a+b}) = 0`).
-/

noncomputable section

open CategoryTheory
open scoped TensorProduct

namespace OddMath.Frontier.EQFunctor

open OddMath.SkewPolynomial (SkewPolynomial generator)
open OddMath.Frontier.EQSkewDifferential
open OddMath.Frontier.EQZab (inclX inclY osymAB par)
open OddMath.Frontier.EQOnhDG (ONH)
open DG MulOpposite TensorProductOver.RightAction


/-! ### Moving `P^a` past polynomials -/

section Chi

variable {a b : ℕ}

variable (a b) in
/-- The signs of `P^a f = χ(f) P^a`: `((-1)^b)^a` on `x`, `((-1)^{b-1})^a` on `y`. -/
def chiCoeff (i : Fin ((a + 2) + (b + 2))) : ℤ :=
  if i.val < a + 2 then ((-1 : ℤ) ^ (b + 2)) ^ (a + 2) else ((-1 : ℤ) ^ (b + 2 - 1)) ^ (a + 2)

variable (a b) in
/-- `χ`: `x_i ↦ ((-1)^b)^a x_i`, `y_j ↦ ((-1)^{b-1})^a y_j`. -/
def chi : SkewPolynomial ((a + 2) + (b + 2)) →+* SkewPolynomial ((a + 2) + (b + 2)) :=
  EQZab.diagHom _ (chiCoeff a b)

theorem chiCoeff_sq (i : Fin ((a + 2) + (b + 2))) : chiCoeff a b i * chiCoeff a b i = 1 := by
  unfold chiCoeff
  split_ifs <;> rw [← mul_pow, ← mul_pow] <;> simp

theorem generator_mul_PA (i : Fin ((a + 2) + (b + 2))) :
    generator i * PA a b = chiCoeff a b i • (PA a b * generator i) := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) i
  · have h := inclX_generator_mul_PA (a := a) (b := b) i
    rw [EQZab.inclX_generator] at h
    rw [h, chiCoeff]
    simp
  · have h := inclY_generator_mul_PA (a := a) (b := b) j
    rw [EQZab.inclY_generator] at h
    rw [h, chiCoeff]
    simp

theorem PA_mul_generator (i : Fin ((a + 2) + (b + 2))) :
    PA a b * generator i = chiCoeff a b i • (generator i * PA a b) := by
  rw [generator_mul_PA, smul_smul, chiCoeff_sq, one_smul]

/-- `P^a f = χ(f) P^a`. -/
theorem PA_mul (f : SkewPolynomial ((a + 2) + (b + 2))) : PA a b * f = chi a b f * PA a b := by
  induction f using induction_generator with
  | hgen i => rw [PA_mul_generator, chi, EQZab.diagHom_generator, smul_mul_assoc]
  | h0 => rw [map_zero, EQBorel.sp_mul_zero, EQBorel.sp_zero_mul]
  | h1 => rw [map_one, sp_mul_one', sp_one_mul']
  | hadd f g hf hg => rw [mul_add, hf, hg, map_add, add_mul]
  | hneg f hf => rw [mul_neg, hf, map_neg, neg_mul]
  | hmul f g hf hg => rw [← EQBorel.sp_mul_assoc, hf, EQBorel.sp_mul_assoc, hg, ← EQBorel.sp_mul_assoc, map_mul]

end Chi

/-! ### Linear forms -/

section LinearForms

theorem sAlpha_add' {N : ℕ} (c c' : Fin N → ℤ) : sAlpha c + sAlpha c' = sAlpha (c + c') := by
  simp only [sAlpha, ← Finset.sum_add_distrib, Pi.add_apply, add_smul]

theorem zsmul_sAlpha {N : ℕ} (k : ℤ) (c : Fin N → ℤ) : k • sAlpha c = sAlpha (k • c) := by
  simp only [sAlpha, Finset.smul_sum, smul_smul, Pi.smul_apply, smul_eq_mul]

theorem diagHom_sAlpha {N : ℕ} (c' c : Fin N → ℤ) : EQZab.diagHom N c' (sAlpha c) = sAlpha (c' * c) := by
  simp only [sAlpha, map_sum, map_zsmul, EQZab.diagHom_generator, smul_smul, Pi.mul_apply, mul_comm]

theorem sAlpha_ext {N : ℕ} {c c' : Fin N → ℤ} (h : ∀ i, c i = c' i) : sAlpha c = sAlpha c' := by
  rw [funext h]

theorem sAlpha_split {A B : ℕ} (c : Fin (A + B) → ℤ) :
    sAlpha c = (∑ i : Fin A, c (Fin.castAdd B i) • generator (Fin.castAdd B i)) +
      ∑ j : Fin B, c (Fin.natAdd A j) • generator (Fin.natAdd A j) := by
  rw [sAlpha, Fin.sum_univ_add]

theorem e1Y_eq_sAlpha (A B : ℕ) : e1Y A B = sAlpha (fun i : Fin (A + B) => if A ≤ i.val then 1 else 0) := by
  rw [sAlpha_split, Finset.sum_eq_zero fun i _ => by simp [Nat.not_le.mpr i.isLt], zero_add, e1Y,
    elementary, EQZab.strictSum_one, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem inclY_theta_e1_eq_sAlpha (A B : ℕ) : inclY A B (theta B (elementary B 1)) =
    sAlpha (fun i : Fin (A + B) => if A ≤ i.val then (-1 : ℤ) ^ (i.val - A) else 0) := by
  rw [sAlpha_split, Finset.sum_eq_zero fun i _ => by simp [Nat.not_le.mpr i.isLt], zero_add,
    elementary, EQZab.strictSum_one, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

end LinearForms

/-! ### `d(P^a) = s_β P^a` in `Z_{a+b}` -/

section DPA

variable {a b : ℕ}

/-- `d_α(P^a) = s_β P^a`: in `Z_{a+b}`, `d(P^a 1_z) = s_β P^a 1_z` with `β = (0,1,0,…) ⊔ (0,1,0,…)`. -/
theorem dAlpha_PA : dAlpha (zAlpha ((a + 2) + (b + 2))) (PA a b) = sAlpha (zAB (a + 2) (b + 2)) * PA a b := by
  rw [dAlpha_apply, d_topY_pow, parityInv_of_mem (topY_pow_mem_grading _), smul_mul_assoc, PA_mul,
    ← smul_mul_assoc, ← smul_mul_assoc, ← add_mul]
  congr 1
  rw [chi, diagHom_sAlpha, e1Y_eq_sAlpha, zsmul_sAlpha, zsmul_sAlpha, sAlpha_add']
  refine sAlpha_ext fun i => ?_
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul, chiCoeff, zAlpha, zAB, par]
  rw [koszulSign_eq_neg_one_pow_natAbs, show ((b + 2 : ℕ) : ℤ) * ((a + 2 : ℕ) : ℤ) =
    (((b + 2) * (a + 2) : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast]
  have hx : (-1 : ℤ) ^ ((b + 2) * (a + 2)) * ((-1) ^ (b + 2)) ^ (a + 2) = 1 := by
    rw [← pow_mul, ← mul_pow, show (-1 : ℤ) * -1 = 1 by norm_num, one_pow]
  have hy : (-1 : ℤ) ^ ((b + 2) * (a + 2)) * ((-1) ^ (b + 2 - 1)) ^ (a + 2) = (-1) ^ a := by
    rw [← pow_mul, ← pow_add, show (b + 2) * (a + 2) + (b + 2 - 1) * (a + 2) = 2 * ((b + 1) * (a + 2)) + a + 2 by
      rw [show b + 2 - 1 = b + 1 by omega]; ring, pow_add, pow_add, pow_mul]
    norm_num
  by_cases hi : i.val < a + 2
  · simp only [show ¬ (a + 2 ≤ i.val) by omega, hi, ↓reduceIte]
    rw [mul_zero, zero_add, ← mul_assoc, hx, one_mul]
  · simp only [show a + 2 ≤ i.val by omega, hi, ↓reduceIte]
    rw [mul_one, ← mul_assoc, hy]
    obtain ⟨m, hm⟩ : ∃ m, i.val = a + 2 + m := ⟨i.val - (a + 2), by omega⟩
    rw [hm, show a + 2 + m - (a + 2) = m by omega]
    rcases Nat.even_or_odd a with ha | ha
    · rw [ha.neg_one_pow, show (a + 2) % 2 = 0 by have := Nat.even_iff.mp ha; omega,
        show (a + 2 + m) % 2 = m % 2 by have := Nat.even_iff.mp ha; omega]
      simp
    · rw [ha.neg_one_pow, show (a + 2) % 2 = 1 by have := Nat.odd_iff.mp ha; omega]
      rcases Nat.mod_two_eq_zero_or_one m with hm2 | hm2
      · rw [show (a + 2 + m) % 2 = 1 by have := Nat.odd_iff.mp ha; omega, hm2]; norm_num
      · rw [show (a + 2 + m) % 2 = 0 by have := Nat.odd_iff.mp ha; omega, hm2]; norm_num

theorem dAlpha_mul_PA (g : SkewPolynomial ((a + 2) + (b + 2))) :
    dAlpha (zAlpha ((a + 2) + (b + 2))) (g * PA a b) = dAlpha (zAB (a + 2) (b + 2)) g * PA a b := by
  rw [dAlpha_mul, dAlpha_PA, dAlpha_apply, add_mul, EQBorel.sp_mul_assoc]

/-- `(θ_a ⊗ θ_b) ∘ (w₀ × w₀) ∘ swap = ι^{ab} ∘ χ ∘ (θ ∘ w₀)` on `OPol_{a+b}`. -/
theorem tau_blockRev_swap :
    (EQZab.tauAB (a + 2) (b + 2)).comp ((blockRev (a + 2) (b + 2)).comp (swapPoly (a + 2) (b + 2))) =
      (parityInv ((a + 2) + (b + 2)) ^ ((a + 2) * (b + 2))).comp
        ((chi a b).comp (twistRev ((a + 2) + (b + 2)))) := by
  refine ringHom_ext fun j => ?_
  simp only [RingHom.comp_apply, swapPoly_generator, blockRev_generator, tauAB_generator, twistRev_generator,
    map_zsmul, chi, EQZab.diagHom_generator, smul_smul, pow_parityInv_generator]
  have hperm : blockRevPerm (a + 2) (b + 2) (swapFin (a + 2) (b + 2) j) = j.rev := by
    apply Fin.ext
    unfold swapFin
    split_ifs with h
    · have := blockRevPerm_natAdd (a + 2) (b + 2) ⟨j.val, h⟩
      rw [show (⟨a + 2 + j.val, by omega⟩ : Fin ((a + 2) + (b + 2))) = Fin.natAdd (a + 2) ⟨j.val, h⟩ from rfl,
        this]
      simp; omega
    · have := blockRevPerm_castAdd (a + 2) (b + 2) ⟨j.val - (b + 2), by omega⟩
      rw [show (⟨j.val - (b + 2), by omega⟩ : Fin ((a + 2) + (b + 2))) =
        Fin.castAdd (b + 2) ⟨j.val - (b + 2), by omega⟩ from rfl, this]
      simp; omega
  rw [hperm]
  congr 1
  generalize j.rev = k
  unfold EQZab.tauCoeff chiCoeff
  by_cases hk : k.val < a + 2
  · simp only [show ¬ (a + 2 ≤ k.val) by omega, hk, ↓reduceIte]
    rw [mul_assoc, ← pow_mul, ← pow_add, show (b + 2) * (a + 2) + (a + 2) * (b + 2) =
      2 * ((a + 2) * (b + 2)) by ring, pow_mul]
    norm_num
  · simp only [show a + 2 ≤ k.val by omega, hk, ↓reduceIte]
    obtain ⟨m, hm⟩ : ∃ m, k.val = a + 2 + m := ⟨k.val - (a + 2), by omega⟩
    rw [hm, show a + 2 + m - (a + 2) = m by omega, show b + 2 - 1 = b + 1 by omega, ← pow_mul,
      mul_assoc, ← pow_add, ← pow_add, show a + 2 + m + ((b + 1) * (a + 2) + (a + 2) * (b + 2)) =
        m + 2 * ((a + 2) * (b + 2)) by ring, pow_add, pow_mul]
    norm_num

end DPA

/-! ### `Z^♮_{a,b}` and `Θ : (Z_a ⊠ Z_b) ⊗ Z^♮_{a,b} → Z_{a+b}` -/

section Theta

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-- `OΛ_{a+b} → OΛ_a ⊗ OΛ_b`, `h ↦ h(y, x)`. -/
def swapDG : osymDG ((a + 2) + (b + 2)) →ᵈᵍ+* (Λa ᵍ⊗[ℤ] Λb) :=
  (tensorEquivOsymAB (a + 2) (b + 2)).symm.toDGAlgHom.toDGRingHom.comp (swapOsym (a + 2) (b + 2))

/-- **`Z^♮_{a,b}`** (Definition 4.15): `OΛ_a ⊗ OΛ_b` as a dg `(OΛ_a ⊗ OΛ_b, OΛ_{a+b})`-bimodule, with
`OΛ_{a+b}` acting on the right through `h ↦ h(y, x)`. -/
abbrev ZNat : Type := (swapDG a b).Bimodule

variable {a b}

theorem rHat_swapDG (h : osymDG ((a + 2) + (b + 2))) :
    rHat (swapDG a b h) = swapPoly (a + 2) (b + 2) (EQFix.toSkew h) := by
  have h1 : tensorToOsymAB (a + 2) (b + 2) (swapDG a b h) = swapOsym (a + 2) (b + 2) h :=
    (tensorEquivOsymAB_apply _).symm.trans ((tensorEquivOsymAB (a + 2) (b + 2)).apply_symm_apply _)
  rw [rHat, ← coe_tensorToOsymAB, h1]
  rfl

/-- `y ⊗ r ↦ (y · r)(x, y)`, without `P^a`. -/
def thetaCFun : ZZ a b →+ ZNat a b →+ SkewPolynomial ((a + 2) + (b + 2)) :=
  AddMonoidHom.mk' (fun y => AddMonoidHom.mk' (fun r => polyHom (op ((swapDG a b).bimoduleEquiv.symm r) • y))
      fun r r' => by rw [map_add, MulOpposite.op_add, add_smul, map_add])
    fun y y' => AddMonoidHom.ext fun r => by
      change polyHom (op _ • (y + y')) = polyHom (op _ • y) + polyHom (op _ • y')
      rw [smul_add, map_add]

theorem thetaCFun_balanced (r' : Λa ᵍ⊗[ℤ] Λb) (y : ZZ a b) (r : ZNat a b) :
    thetaCFun (op r' • y) r = thetaCFun y (r' • r) := by
  change polyHom (op _ • op r' • y) = polyHom (op ((swapDG a b).bimoduleEquiv.symm (r' • r)) • y)
  rw [← mul_smul, ← op_mul]
  rfl

/-- `Θ_c : (Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b} → OPol_{a+b}`, `y ⊗ r ↦ (y r)(x, y)`. -/
def thetaC : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b) →+ SkewPolynomial ((a + 2) + (b + 2)) :=
  TensorProductOver.lift thetaCFun thetaCFun_balanced

theorem thetaC_tmul (y : ZZ a b) (r : ZNat a b) :
    thetaC (TensorProductOver.tmul _ y r) = polyHom (op ((swapDG a b).bimoduleEquiv.symm r) • y) := rfl

/-- The right action of `h ∈ OΛ_{a+b}` on `Z^♮` becomes right multiplication by
`(θ_a ⊗ θ_b)((w₀ × w₀)(h(y, x)))`. -/
theorem thetaC_op_smul (h : osymDG ((a + 2) + (b + 2)))
    (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaC (op h • t) = thetaC t * EQZab.tauAB (a + 2) (b + 2)
      (blockRev (a + 2) (b + 2) (swapPoly (a + 2) (b + 2) (EQFix.toSkew h))) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, EQBorel.sp_zero_mul]
  | tmul y r =>
    rw [TensorProductOver.op_smul_tmul_right, thetaC_tmul, thetaC_tmul]
    change polyHom (op ((swapDG a b).bimoduleEquiv.symm r * swapDG a b h) • y) = _
    rw [op_mul, mul_smul, polyHom_op_smul, rHat_swapDG]
  | add t t' ht ht' => rw [smul_add, map_add, map_add, ht, ht', add_mul]

theorem thetaC_surjective : Function.Surjective (thetaC (a := a) (b := b)) := fun F => by
  obtain ⟨y, hy⟩ := polyHom_bijective.2 F
  exact ⟨TensorProductOver.tmul _ y ((swapDG a b).bimoduleEquiv 1), by
    rw [thetaC_tmul, DGRingHom.Bimodule.bimoduleEquiv_symm_apply, op_one, one_smul, hy]⟩

theorem thetaC_mem {k : ℤ} {t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)}
    (ht : t ∈ DG.grading k) : thetaC t ∈ grading ((a + 2) + (b + 2)) k := by
  refine TensorProductOver.induction_on_mem_grading (P := fun t => thetaC t ∈ grading _ k) ?_ ?_ ?_ ?_ ht
  · rw [map_zero]; exact zero_mem _
  · intro i j y r hy hr hij
    rw [thetaC_tmul, ← hij]
    exact polyHom_mem (op_smul_mem_grading (M := ZZ a b) hr hy)
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

theorem zE_thetaC_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    zE ((a + 2) + (b + 2)) (thetaC (s • t)) = ONH.iota a b s • zE ((a + 2) + (b + 2)) (thetaC t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, map_zero, smul_zero]
  | tmul y r =>
    rw [TensorProductOver.smul_tmul, thetaC_tmul, thetaC_tmul, ← DGBimodule.smul_op_smul, zE_polyHom_smul]
  | add t t' ht ht' =>
    rw [show s • (t + t') = s • t + s • t' from smul_add s t t', map_add, map_add, ht, ht', map_add,
      map_add, smul_add]

theorem thetaC_tmul_d (y : ZZ a b) {i : ℤ} (hy : y ∈ DG.grading i) (r : Λa ᵍ⊗[ℤ] Λb) :
    thetaC (DG.d (TensorProductOver.tmul _ y ((swapDG a b).bimoduleEquiv r))) =
      dAlpha (zAB (a + 2) (b + 2)) (thetaC (TensorProductOver.tmul _ y ((swapDG a b).bimoduleEquiv r))) := by
  have h1 := TensorProductOver.d_tmul_of_mem (A := Λa ᵍ⊗[ℤ] Λb) hy ((swapDG a b).bimoduleEquiv r)
  have e1 : polyHom (DG.d (op r • y)) = dAlpha (zAB (a + 2) (b + 2)) (polyHom (op r • y)) := polyHom_d _
  have e2 : DG.d (op r • y) = op r • DG.d y + koszulSign i • (op (DG.d r) • y) := d_op_smul hy r
  rw [h1, map_add, map_units_zsmul]
  change polyHom (op r • DG.d y) + koszulSign i • polyHom (op (DG.d r) • y) =
    dAlpha (zAB (a + 2) (b + 2)) (polyHom (op r • y))
  rw [← map_units_zsmul, ← map_add, ← e2, e1]

theorem thetaC_d (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaC (DG.d t) = dAlpha (zAB (a + 2) (b + 2)) (thetaC t) := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, map_zero]
  | tmul y r =>
    obtain ⟨r, rfl⟩ := (swapDG a b).bimoduleEquiv.surjective r
    induction y using DG.induction_on with
    | h_zero => rw [TensorProductOver.zero_tmul, d_zero, map_zero, map_zero]
    | @h_homogeneous i y => exact thetaC_tmul_d (y : ZZ a b) y.2 _
    | h_add y y' hy hy' => simp only [TensorProductOver.add_tmul, map_add, hy, hy']
  | add t t' ht ht' => simp only [map_add, ht, ht']

/-- The inverse of `Θ_c`: `F ↦ (u ⊠ v) ⊗ 1` for `F = u(x) v(y)`. -/
def thetaCInv : SkewPolynomial ((a + 2) + (b + 2)) →+ TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b) :=
  AddMonoidHom.mk' (fun F => TensorProductOver.tmul _ (polyEquiv.symm F) ((swapDG a b).bimoduleEquiv 1))
    fun F F' => by rw [map_add, TensorProductOver.add_tmul]

theorem thetaC_thetaCInv (F : SkewPolynomial ((a + 2) + (b + 2))) : thetaC (thetaCInv F) = F := by
  change thetaC (TensorProductOver.tmul _ _ _) = F
  rw [thetaC_tmul, DGRingHom.Bimodule.bimoduleEquiv_symm_apply, op_one, one_smul, ← polyEquiv_apply,
    AddEquiv.apply_symm_apply]

theorem thetaCInv_thetaC (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaCInv (thetaC t) = t := by
  induction t using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul y r =>
    rw [thetaC_tmul]
    change TensorProductOver.tmul _ (polyEquiv.symm (polyEquiv _)) _ = _
    rw [AddEquiv.symm_apply_apply]
    conv_rhs => rw [show r = (swapDG a b).bimoduleEquiv.symm r • (swapDG a b).bimoduleEquiv 1 from by
      rw [DGRingHom.Bimodule.smul_bimoduleEquiv, mul_one]; rfl]
    rw [← TensorProductOver.op_smul_tmul]
  | add t t' ht ht' => rw [map_add, map_add, ht, ht']

theorem thetaC_injective : Function.Injective (thetaC (a := a) (b := b)) :=
  Function.LeftInverse.injective thetaCInv_thetaC

end Theta

/-! ### Cancellation of `P^a` -/

section Cancel

theorem generator_mul_apply {N : ℕ} (j : Fin N) (w : SkewPolynomial N) (α : Fin N → ℕ) :
    (generator j * w) (OddMath.SkewPolynomial.expSingle j + α) =
      OddMath.skewSign (OddMath.SkewPolynomial.expSingle j) α * w α := by
  induction w using Finsupp.induction_linear with
  | zero => rw [EQBorel.sp_mul_zero]; simp
  | add f g hf hg => rw [mul_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply, mul_add]
  | single β c =>
    change (OddMath.SkewPolynomial.mul (OddMath.SkewPolynomial.monomial _ 1)
      (OddMath.SkewPolynomial.monomial β c)) _ = _
    rw [OddMath.SkewPolynomial.mul_monomial, OddMath.SkewPolynomial.monomial, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h : β = α
    · subst h; simp; ring
    · simp only [add_right_inj, h, ↓reduceIte, mul_zero]

theorem generator_mul_eq_zero {N : ℕ} {j : Fin N} {w : SkewPolynomial N} (h : generator j * w = 0) :
    w = 0 := by
  ext α
  have := generator_mul_apply j w α
  rw [h, Finsupp.coe_zero, Pi.zero_apply] at this
  have hs : OddMath.skewSign (OddMath.SkewPolynomial.expSingle j) α ≠ 0 := by
    unfold OddMath.skewSign; exact pow_ne_zero _ (by norm_num)
  exact (mul_eq_zero.mp this.symm).resolve_left hs

theorem list_prod_mul_eq_zero {N : ℕ} :
    ∀ (L : List (Fin N)) {w : SkewPolynomial N}, (L.map generator).prod * w = 0 → w = 0
  | [], w, h => by simpa using h
  | j :: L, w, h => by
    rw [List.map_cons, List.prod_cons, EQBorel.sp_mul_assoc] at h
    exact list_prod_mul_eq_zero L (generator_mul_eq_zero h)

theorem topY_mul_eq_zero {A B : ℕ} {w : SkewPolynomial (A + B)} (h : topY A B * w = 0) : w = 0 := by
  have e : topY A B = ((List.ofFn fun j : Fin B => Fin.natAdd A j).map generator).prod := by
    rw [topY, elementary, strictSum_top, map_list_prod, List.map_ofFn, List.map_ofFn]
    simp [Function.comp_def]
  rw [e] at h
  exact list_prod_mul_eq_zero _ h

/-- `P^m` is not a left zero divisor in `OPol_{a+b}`. -/
theorem topY_pow_mul_eq_zero {A B : ℕ} : ∀ (m : ℕ) {w : SkewPolynomial (A + B)}, topY A B ^ m * w = 0 → w = 0
  | 0, w, h => by simpa using h
  | m + 1, w, h => by
    rw [pow_succ', EQBorel.sp_mul_assoc] at h
    exact topY_pow_mul_eq_zero m (topY_mul_eq_zero h)

variable {a b : ℕ}

/-- `P^a` is killed by the crossings inside the two blocks. -/
theorem blockSym_PA : EQZab.BlockSym (a + 2 + b) (a + 2) (PA a b) := by
  intro i hi
  rcases hi with hi | hi
  · have := divided_PA_x (a := a) (b := b) ⟨i.val, by omega⟩
    convert this using 3
    exact Fin.ext (by rw [OnhWindow.shiftIndex_val]; simp)
  · have := divided_PA_y (a := a) (b := b) ⟨i.val - (a + 2), by omega⟩
    convert this using 3
    exact Fin.ext (by rw [OnhWindow.shiftIndex_val]; simp only; omega)

/-- `P^a` is not a left zero divisor in `ONH_{a+b}`. -/
theorem Pw_mul_eq_zero {h : ONH (a + 2 + b)} (hh : Pw a b * h = 0) : h = 0 := by
  apply EQOnhDG.ONH.eq_zero_of_forall_smul_eq_zero
  intro z
  have h1 : (Pw a b * h) • z = 0 := by rw [hh, zero_smul]
  rw [mul_smul] at h1
  apply (zE _).symm.injective
  rw [map_zero]
  apply topY_pow_mul_eq_zero (A := a + 2) (B := b + 2) (a + 2)
  have h2 := congrArg (zE ((a + 2) + (b + 2))).symm h1
  rw [map_zero, zE_symm_onh_smul] at h2
  rw [← h2]
  change _ = NilHeckeAction.action (a + 2 + b) (OnhPolynomial.polyElem _ (PA a b)) _
  rw [OnhPolynomial.action_polyElem]
  rfl

end Cancel

/-! ### `Θ = Θ_c · P^a : (Z_a ⊠ Z_b) ⊗ Z^♮_{a,b} → Z_{a+b}` -/

section ThetaP

variable {a b : ℕ}

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

theorem chi_chi (f : SkewPolynomial ((a + 2) + (b + 2))) : chi a b (chi a b f) = f := by
  have h : (chi a b).comp (chi a b) = RingHom.id _ := ringHom_ext fun j => by
    rw [RingHom.comp_apply, chi, EQZab.diagHom_generator, map_zsmul, EQZab.diagHom_generator, smul_smul,
      chiCoeff_sq, one_smul, RingHom.id_apply]
  exact RingHom.congr_fun h f

theorem chi_mem_grading {k : ℤ} {f : SkewPolynomial ((a + 2) + (b + 2))} (hf : f ∈ grading _ k) :
    chi a b f ∈ grading _ k :=
  ringHom_mem_grading _ (fun j => by
    rw [chi, EQZab.diagHom_generator]; exact AddSubgroup.zsmul_mem _ (generator_mem_grading _) _) hf

theorem mul_PA_eq (f : SkewPolynomial ((a + 2) + (b + 2))) : f * PA a b = PA a b * chi a b f := by
  rw [PA_mul, chi_chi]

/-- `Θ(t) = Θ_c(t) P^a ∈ Z_{a+b}`. -/
def thetaP : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b) →+ Zn ((a + 2) + (b + 2)) :=
  AddMonoidHom.mk' (fun t => zE _ (thetaC t * PA a b)) fun t t' => by rw [map_add, add_mul, map_add]

theorem thetaP_apply (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaP t = zE _ (thetaC t * PA a b) := rfl

theorem thetaP_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaP (s • t) = ONH.iota a b s • thetaP t := by
  rw [thetaP_apply, thetaP_apply]
  apply (zE _).symm.injective
  rw [zE_symm_iota_smul_mul s _ _ blockSym_PA, ← zE_thetaC_smul, AddEquiv.symm_apply_apply,
    AddEquiv.symm_apply_apply]

theorem thetaP_d (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaP (DG.d t) = DG.d (thetaP t) := by
  rw [thetaP_apply, thetaP_apply, thetaC_d]
  apply (zE _).symm.injective
  rw [OPolAlpha.symm_d, indicator_oddStrands, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    dAlpha_mul_PA]

theorem thetaP_mem {k : ℤ} {t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)}
    (ht : t ∈ DG.grading k) : thetaP t ∈ DG.grading (k + degP a b) := by
  rw [thetaP_apply]
  refine OPolAlpha.mem_grading_iff.mpr ?_
  rw [AddEquiv.symm_apply_apply]
  have h := topY_pow_mem_grading (A := a + 2) (B := b + 2) (a + 2)
  exact mul_mem_grading' (thetaC_mem ht) h

variable (a b) in
/-- `ab`. -/
abbrev nAB : ℕ := (a + 2) * (b + 2)

theorem thetaP_op_smul {k : ℤ} {h : osymDG ((a + 2) + (b + 2))} (hh : h ∈ DG.grading k)
    (t : TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)) :
    thetaP (op h • t) = ((koszulSign k : ℤ) ^ nAB a b) • (op h • thetaP t) := by
  rw [thetaP_apply, thetaP_apply, thetaC_op_smul]
  apply (zE _).symm.injective
  have hk : twistRev ((a + 2) + (b + 2)) (EQFix.toSkew h) ∈ grading _ k :=
    twistRev_mem_grading (EQFix.Zab.toSkew_mem_grading (a := a + 2) (b := b + 2) hh)
  have hτ := RingHom.congr_fun (tau_blockRev_swap (a := a) (b := b)) (EQFix.toSkew h)
  simp only [RingHom.comp_apply] at hτ
  rw [hτ, pow_parityInv_of_mem _ (chi_mem_grading hk), AddEquiv.symm_apply_apply, map_zsmul,
    EQSkewDifferential.Zn.op_smul_osym, EQSkewDifferential.Zn.symm_op_smul, AddEquiv.symm_apply_apply,
    mul_smul_comm, smul_mul_assoc, EQBorel.sp_mul_assoc, mul_PA_eq, chi_chi, ← EQBorel.sp_mul_assoc]
  rfl

end ThetaP

/-! ### `((Z_a ⊠ Z_b) ⊗ Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}` -/

section Compare

variable {a b : ℕ}

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

variable (a b) in
/-- `(Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}`. -/
abbrev TT : Type := TensorProductOver (Λa ᵍ⊗[ℤ] Λb) (ZZ a b) (ZNat a b)

variable (a b) in
/-- `Z_{a+b}^∨`. -/
abbrev ZD : Type := RightDual (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2)))

variable (a b) in
theorem hFull : FullAction (ONH (a + 2 + b)) (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) :=
  EQOnhDG.ONH.fullAction (a + 2 + b)

theorem koszulSign_natCast_mul (m : ℕ) (k : ℤ) : (koszulSign ((m : ℤ) * k) : ℤ) = (koszulSign k : ℤ) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.cast_succ, add_mul, one_mul, koszulSign_add, Units.val_mul, ih, pow_succ]

theorem koszulSign_degP_mul (k : ℤ) : (koszulSign (degP a b * k) : ℤ) = (koszulSign k : ℤ) ^ nAB a b := by
  rw [← koszulSign_natCast_mul]
  congr 2
  simp only [degP, nAB, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  ring

theorem rho_zsmul_left (n : ℤ) (z : Zn ((a + 2) + (b + 2))) (f : ZD a b) :
    (hFull a b).rho (n • z) f = n • (hFull a b).rho z f := by
  change (hFull a b).rhoHom (n • z) f = n • (hFull a b).rhoHom z f
  rw [map_zsmul, AddMonoidHom.smul_apply]

theorem rho_units_smul_right (u : ℤˣ) (z : Zn ((a + 2) + (b + 2))) (f : ZD a b) :
    (hFull a b).rho z (u • f) = (u : ℤ) • (hFull a b).rho z f := by
  change (hFull a b).rhoHom z (u • f) = (u : ℤ) • (hFull a b).rhoHom z f
  rw [Units.smul_def, map_zsmul]

/-- `t ⊗ f ↦ Θ(t) ε^{ab}(f) ∈ ONH_{a+b}`, through the full action of `ONH_{a+b}` on `Z_{a+b}`. -/
def gFun : TT a b →+ ZD a b →+ ONH (a + 2 + b) :=
  ((hFull a b).rhoHom.comp thetaP).compl₂ (signTwist (ZD a b) (degP a b))

theorem gFun_apply (t : TT a b) (f : ZD a b) :
    gFun t f = (hFull a b).rho (thetaP t) (signTwist (ZD a b) (degP a b) f) := rfl

theorem gFun_balanced (h : osymDG ((a + 2) + (b + 2))) (t : TT a b) (f : ZD a b) :
    gFun (op h • t) f = gFun t (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [gFun_apply, gFun_apply, thetaP_op_smul h.2, rho_zsmul_left, (hFull a b).rho_balanced,
      signTwist_smul_of_mem _ h.2, rho_units_smul_right, koszulSign_degP_mul]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

/-- `G₀ : ((Z_a ⊠ Z_b) ⊗ Z^♮) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ → ONH_{a+b}`, `t ⊗ f ↦ Θ(t) ε^{ab}(f)`. -/
def gHom : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) →+ ONH (a + 2 + b) :=
  TensorProductOver.lift gFun gFun_balanced

theorem gHom_tmul (t : TT a b) (f : ZD a b) :
    gHom (TensorProductOver.tmul _ t f) = (hFull a b).rho (thetaP t) (signTwist (ZD a b) (degP a b) f) :=
  rfl

set_option maxHeartbeats 1600000 in
theorem gHom_smul (s : 𝒪a ᵍ⊗[ℤ] 𝒪b) (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gHom (s • x) = ONH.iota a b s * gHom x := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, mul_zero]
  | tmul t f => rw [TensorProductOver.smul_tmul, gHom_tmul, gHom_tmul, thetaP_smul, (hFull a b).rho_smul_left]
  | add x y hx hy =>
    rw [show s • (x + y) = s • x + s • y from smul_add s x y, map_add, map_add, hx, hy, mul_add]

set_option maxHeartbeats 1600000 in
theorem gHom_op_smul {i : ℤ} {g : ONH (a + 2 + b)} (hg : g ∈ DG.grading i)
    (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gHom (op g • x) = koszulSign (degP a b * i) • (gHom x * g) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [smul_zero, map_zero, zero_mul, smul_zero]
  | tmul t f =>
    rw [TensorProductOver.op_smul_tmul_right, gHom_tmul, gHom_tmul, signTwist_op_smul_of_mem _ hg,
      rho_units_smul_right, (hFull a b).rho_op_smul, Units.smul_def]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, add_mul, smul_add]

set_option maxHeartbeats 1600000 in
theorem gHom_mem {k : ℤ} {x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)}
    (hx : x ∈ DG.grading k) : gHom x ∈ DG.grading (k + degP a b) := by
  refine TensorProductOver.induction_on_mem_grading (P := fun x => gHom x ∈ DG.grading (k + degP a b))
    ?_ ?_ ?_ ?_ hx
  · rw [map_zero]; exact zero_mem _
  · intro i j t f ht hf hij
    rw [gHom_tmul, ← hij, show i + j + degP a b = i + degP a b + j by ring]
    exact (hFull a b).rho_mem (thetaP_mem ht) (signTwist_mem _ hf)
  · intro x y hx hy; rw [map_add]; exact add_mem hx hy
  · intro x hx; rw [map_neg]; exact neg_mem hx

set_option maxHeartbeats 1600000 in
theorem gHom_tmul_d {i j : ℤ} {t : TT a b} (ht : t ∈ DG.grading i) {f : ZD a b} (hf : f ∈ DG.grading j) :
    gHom (DG.d (TensorProductOver.tmul _ t f)) = DG.d (gHom (TensorProductOver.tmul _ t f)) := by
  have h1 := TensorProductOver.d_tmul_of_mem (A := osymDG ((a + 2) + (b + 2))) (N := ZD a b) ht f
  rw [h1]
  rw [map_add]
  rw [map_units_zsmul]
  rw [gHom_tmul]
  rw [gHom_tmul]
  rw [gHom_tmul]
  have h2 := thetaP_mem ht
  have h3 := signTwist_mem (degP a b) hf
  have h4 := (hFull a b).d_rho h2 h3
  rw [h4]
  rw [d_signTwist, rho_units_smul_right, thetaP_d]
  rw [Units.smul_def, Units.smul_def, smul_smul, ← Units.val_mul, ← koszulSign_add]
  have e : koszulSign (i + degP a b + degP a b) = koszulSign i := by
    rw [add_assoc, ← two_mul, koszulSign_add, show koszulSign (2 * degP a b) = 1 from Int.negOnePow_two_mul _,
      mul_one]
  rw [e]

set_option maxHeartbeats 1600000 in
theorem gHom_d (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gHom (DG.d x) = DG.d (gHom x) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [d_zero, map_zero, d_zero]
  | tmul t f =>
    induction t using DG.induction_on with
    | h_zero => rw [TensorProductOver.zero_tmul, d_zero, map_zero, d_zero]
    | @h_homogeneous i t =>
      induction f using DG.induction_on with
      | h_zero => rw [TensorProductOver.tmul_zero, d_zero, map_zero, d_zero]
      | @h_homogeneous j f => exact gHom_tmul_d t.2 f.2
      | h_add f f' hf hf' => rw [TensorProductOver.tmul_add, d_add, map_add, hf, hf', map_add, d_add]
    | h_add t t' ht ht' => rw [TensorProductOver.add_tmul, d_add, map_add, ht, ht', map_add, d_add]
  | add x y hx hy => rw [d_add, map_add, hx, hy, map_add, d_add]

end Compare

/-! ### Bijectivity: `G₀ = P^a · μ ∘ Θ₁` -/

section Bij

variable {a b : ℕ}

theorem zE_symm_Pw_smul (z : Zn ((a + 2) + (b + 2))) :
    (zE ((a + 2) + (b + 2))).symm (Pw a b • z) = PA a b * (zE ((a + 2) + (b + 2))).symm z := by
  rw [zE_symm_onh_smul]
  change NilHeckeAction.action (a + 2 + b) (OnhPolynomial.polyElem _ (PA a b)) _ = _
  rw [OnhPolynomial.action_polyElem]

theorem Pw_smul_eq_zero {z : Zn ((a + 2) + (b + 2))} (h : Pw a b • z = 0) : z = 0 := by
  apply (zE ((a + 2) + (b + 2))).symm.injective
  rw [map_zero]
  apply topY_pow_mul_eq_zero (A := a + 2) (B := b + 2) (a + 2)
  rw [← zE_symm_Pw_smul, h, map_zero]

/-- `Θ₁(t) = χ(Θ_c t)`, so that `Θ = P^a Θ₁` (`thetaP_eq`). -/
def theta1 : TT a b →+ Zn ((a + 2) + (b + 2)) :=
  AddMonoidHom.mk' (fun t => zE _ (chi a b (thetaC t))) fun t t' => by rw [map_add, map_add, map_add]

theorem theta1_apply (t : TT a b) : theta1 t = zE _ (chi a b (thetaC t)) := rfl

theorem thetaP_eq (t : TT a b) : thetaP t = Pw a b • theta1 t := by
  apply (zE ((a + 2) + (b + 2))).symm.injective
  rw [zE_symm_Pw_smul, thetaP_apply, theta1_apply, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
    mul_PA_eq]

theorem Pw_smul_zsmul (n : ℤ) (z : Zn ((a + 2) + (b + 2))) : Pw a b • (n • z) = n • (Pw a b • z) :=
  map_zsmul (DistribSMul.toAddMonoidHom (Zn ((a + 2) + (b + 2))) (Pw a b)) n z

theorem theta1_op_smul {k : ℤ} {h : osymDG ((a + 2) + (b + 2))} (hh : h ∈ DG.grading k) (t : TT a b) :
    theta1 (op h • t) = ((koszulSign k : ℤ) ^ nAB a b) • (op h • theta1 t) := by
  have e := thetaP_op_smul hh t
  rw [thetaP_eq, thetaP_eq, ← smul_comm (Pw a b) (op h), ← Pw_smul_zsmul] at e
  exact sub_eq_zero.mp (Pw_smul_eq_zero (by rw [smul_sub, e, sub_self]))

/-- The inverse of `Θ₁`. -/
def theta1Inv : Zn ((a + 2) + (b + 2)) →+ TT a b :=
  AddMonoidHom.mk' (fun z => thetaCInv (chi a b ((zE _).symm z))) fun z z' => by
    rw [map_add, map_add, map_add]

theorem theta1_theta1Inv (z : Zn ((a + 2) + (b + 2))) : theta1 (theta1Inv z) = z := by
  change zE _ (chi a b (thetaC (thetaCInv (chi a b ((zE _).symm z))))) = z
  rw [thetaC_thetaCInv, chi_chi, AddEquiv.apply_symm_apply]

theorem theta1Inv_theta1 (t : TT a b) : theta1Inv (theta1 t) = t := by
  change thetaCInv (chi a b ((zE _).symm (zE _ (chi a b (thetaC t))))) = t
  rw [AddEquiv.symm_apply_apply, chi_chi, thetaCInv_thetaC]

theorem sign_pow_mul_self (k : ℤ) (n : ℕ) : ((koszulSign k : ℤ) ^ n) * ((koszulSign k : ℤ) ^ n) = 1 := by
  rw [← mul_pow, ← Units.val_mul, Int.units_mul_self, Units.val_one, one_pow]

theorem theta1Inv_op_smul {k : ℤ} {h : osymDG ((a + 2) + (b + 2))} (hh : h ∈ DG.grading k)
    (z : Zn ((a + 2) + (b + 2))) :
    theta1Inv (op h • z) = ((koszulSign k : ℤ) ^ nAB a b) • (op h • theta1Inv z) := by
  apply Function.LeftInverse.injective theta1Inv_theta1
  rw [theta1_theta1Inv, map_zsmul, theta1_op_smul hh, theta1_theta1Inv, smul_smul, sign_pow_mul_self, one_smul]

/-- `t ⊗ f ↦ Θ₁(t) ⊗ ε^{ab}(f)`. -/
def oneFun : TT a b →+ ZD a b →+ TensorProductOver (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) (ZD a b) :=
  ((TensorProductOver.tmulAddHom _ _ _).comp theta1).compl₂ (signTwist (ZD a b) (degP a b))

theorem oneFun_apply (t : TT a b) (f : ZD a b) :
    oneFun t f = TensorProductOver.tmul _ (theta1 t) (signTwist (ZD a b) (degP a b) f) := rfl

theorem oneFun_balanced (h : osymDG ((a + 2) + (b + 2))) (t : TT a b) (f : ZD a b) :
    oneFun (op h • t) f = oneFun t (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [oneFun_apply, oneFun_apply, theta1_op_smul h.2, TensorProductOver.zsmul_tmul,
      TensorProductOver.op_smul_tmul, signTwist_smul_of_mem _ h.2, TensorProductOver.tmul_units_smul,
      Units.smul_def, koszulSign_degP_mul]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

/-- `Θ₁ ⊗ ε^{ab}`. -/
def oneHom : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) →+
    TensorProductOver (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) (ZD a b) :=
  TensorProductOver.lift oneFun oneFun_balanced

/-- `z ⊗ f ↦ Θ₁⁻¹(z) ⊗ ε^{ab}(f)`. -/
def invFun : Zn ((a + 2) + (b + 2)) →+ ZD a b →+ TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) :=
  ((TensorProductOver.tmulAddHom _ _ _).comp theta1Inv).compl₂ (signTwist (ZD a b) (degP a b))

theorem invFun_apply (z : Zn ((a + 2) + (b + 2))) (f : ZD a b) :
    invFun z f = TensorProductOver.tmul _ (theta1Inv z) (signTwist (ZD a b) (degP a b) f) := rfl

set_option maxHeartbeats 1600000 in
theorem invFun_balanced (h : osymDG ((a + 2) + (b + 2))) (z : Zn ((a + 2) + (b + 2))) (f : ZD a b) :
    invFun (op h • z) f = invFun z (h • f) := by
  induction h using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | @h_homogeneous k h =>
    rw [invFun_apply, invFun_apply, theta1Inv_op_smul h.2, TensorProductOver.zsmul_tmul,
      TensorProductOver.op_smul_tmul, signTwist_smul_of_mem _ h.2, TensorProductOver.tmul_units_smul,
      Units.smul_def, koszulSign_degP_mul]
  | h_add h h' ih ih' =>
    rw [MulOpposite.op_add, add_smul, map_add, AddMonoidHom.add_apply, ih, ih', add_smul, map_add]

def invHom : TensorProductOver (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) (ZD a b) →+
    TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) :=
  TensorProductOver.lift invFun invFun_balanced

theorem invHom_oneHom (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    invHom (oneHom x) = x := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul t f =>
    change TensorProductOver.tmul _ (theta1Inv (theta1 t))
      (signTwist (ZD a b) (degP a b) (signTwist (ZD a b) (degP a b) f)) = _
    rw [theta1Inv_theta1, signTwist_signTwist]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem oneHom_invHom (y : TensorProductOver (osymDG ((a + 2) + (b + 2))) (Zn ((a + 2) + (b + 2))) (ZD a b)) :
    oneHom (invHom y) = y := by
  induction y using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul z f =>
    change TensorProductOver.tmul _ (theta1 (theta1Inv z))
      (signTwist (ZD a b) (degP a b) (signTwist (ZD a b) (degP a b) f)) = _
    rw [theta1_theta1Inv, signTwist_signTwist]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

set_option maxHeartbeats 800000 in
theorem gHom_eq (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gHom x = Pw a b * (hFull a b).mulHom (oneHom x) := by
  induction x using TensorProductOver.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, mul_zero]
  | tmul t f =>
    rw [gHom_tmul, thetaP_eq, (hFull a b).rho_smul_left]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, map_add, mul_add]

theorem gHom_injective : Function.Injective (gHom (a := a) (b := b)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [gHom_eq] at hx
  have h1 := (hFull a b).mulHom_injective (znRightBasis ((a + 2) + (b + 2)))
    ((Pw_mul_eq_zero hx).trans (map_zero _).symm)
  rw [← invHom_oneHom x, h1, map_zero]

theorem exists_gHom_eq (g : ONH (a + 2 + b)) : ∃ x, gHom x = Pw a b * g := by
  obtain ⟨y, hy⟩ := (hFull a b).mulHom_surjective (znRightBasis ((a + 2) + (b + 2))) g
  exact ⟨invHom y, by rw [gHom_eq, oneHom_invHom, hy]⟩

end Bij

/-! ### The isomorphism `G : ((Z_a ⊠ Z_b) ⊗ Z^♮) ⊗ Z_{a+b}^∨ ≅ ONH^♮` -/

section GEquiv

variable {a b : ℕ}

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)

theorem gHom_mem_natSub (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    (show IONH a b from gHom x) ∈ natSub a b :=
  ⟨_, gHom_eq x⟩

/-- `G₀` as a map into `P^a ONH_{a+b}`. -/
def gNat : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) →+ natSub a b :=
  AddMonoidHom.mk' (fun x => ⟨gHom x, gHom_mem_natSub x⟩) fun x y => Subtype.ext (map_add gHom x y)

theorem coe_gNat (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    ((gNat x : natSub a b) : IONH a b) = gHom x := rfl

theorem gNat_injective : Function.Injective (gNat (a := a) (b := b)) := fun _ _ h =>
  gHom_injective (congrArg Subtype.val h)

theorem gNat_surjective : Function.Surjective (gNat (a := a) (b := b)) := fun m => by
  obtain ⟨g, hg⟩ := m.2
  obtain ⟨x, hx⟩ := exists_gHom_eq g
  exact ⟨x, Subtype.ext (hx.trans hg.symm)⟩

variable (a b) in
/-- `G₀` as a linear map into `ONH^♮`. -/
def gLin : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) →ₗ[𝒪a ᵍ⊗[ℤ] 𝒪b] ONHNat a b where
  toFun x := Regrade.mk (degP a b) (gNat x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' s x := by
    change (gNat (s • x) : natSub a b) = s • gNat x
    exact Subtype.ext (gHom_smul s x)

variable (a b) in
/-- **The bimodule isomorphism behind the restriction half of Corollary 4.21**:
`((Z_a ⊠ Z_b) ⊗_{OΛ_a ⊗ OΛ_b} Z^♮_{a,b}) ⊗_{OΛ_{a+b}} Z_{a+b}^∨ ≅ ONH^♮_{a+b}` as dg
`(ONH_a ⊗ ONH_b, ONH_{a+b})`-bimodules (`gEquiv_op_smul`), `t ⊗ f ↦ Θ(t) ε^{ab}(f)`. -/
def gEquiv : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b) ≃ᵈᵍ[𝒪a ᵍ⊗[ℤ] 𝒪b]
    ONHNat a b where
  toLinearEquiv := LinearEquiv.ofBijective (gLin a b) ⟨fun _ _ h => gNat_injective h, fun m => gNat_surjective m⟩
  map_mem' {k x} hx :=
    show (gNat x : natSub a b) ∈ DG.grading (k + degP a b) from
      (DGSubmodule.mem_grading_iff _).mpr (gHom_mem hx)
  map_d' x := show (gNat (DG.d x) : natSub a b) = DG.d (gNat x) from Subtype.ext (gHom_d x)

theorem gEquiv_apply (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gEquiv a b x = Regrade.mk (degP a b) (gNat x) := rfl

set_option maxHeartbeats 800000 in
theorem gEquiv_op_smul (g : ONH (a + 2 + b))
    (x : TensorProductOver (osymDG ((a + 2) + (b + 2))) (TT a b) (ZD a b)) :
    gEquiv a b (op g • x) = op g • gEquiv a b x := by
  induction g using DG.induction_on with
  | h_zero => rw [op_zero, zero_smul, map_zero, zero_smul]
  | @h_homogeneous i g =>
    rw [gEquiv_apply, gEquiv_apply, Regrade.op_smul_mk_of_mem g.2]
    congr 1
    apply Subtype.ext
    rw [coe_gNat, gHom_op_smul g.2]
    rfl
  | h_add g g' hg hg' => rw [MulOpposite.op_add, add_smul, map_add, hg, hg', add_smul]

end GEquiv

/-! ### The restriction half on abelian categories -/

section RestrictionA

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

/-- **Definition 4.20**: `Res^♮(M) = ONH^♮_{a+b} ⊗_{ONH_{a+b}} M`. -/
abbrev ResNatA : DGModuleCat.{0} (ONH (a + 2 + b)) ⥤ DGModuleCat.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) :=
  DGModuleCat.tensorFunctor (B := ONH (a + 2 + b)) (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONHNat a b)

/-- **Definition 4.15**: `R(M) = Z^♮_{a,b} ⊗_{OΛ_{a+b}} M`, i.e. extension of scalars along `swapDG`. -/
abbrev RA : DGModuleCat.{0} (osymDG ((a + 2) + (b + 2))) ⥤ DGModuleCat.{0} (Λa ᵍ⊗[ℤ] Λb) :=
  DGModuleCat.tensorFunctor (B := osymDG ((a + 2) + (b + 2))) (Λa ᵍ⊗[ℤ] Λb) (ZNat a b)

theorem RA_eq_extendScalars : RA a b = DGModuleCat.extendScalars.{0} (swapDG a b) := rfl

theorem gEquiv_symm_op_smul (g : ONH (a + 2 + b)) (m : ONHNat a b) :
    (gEquiv a b).symm (op g • m) = op g • (gEquiv a b).symm m := by
  apply (gEquiv a b).injective
  rw [gEquiv_op_smul, DGModuleEquiv.apply_symm_apply, DGModuleEquiv.apply_symm_apply]

/-- `Res^♮ ≅ (J^A_2)^{-1} ∘ R ∘ J^A`. -/
def resNatIso :
    ResNatA a b ≅ ((JA (a + 2 + b)).functor : _ ⥤ DGModuleCat.{0} (osymDG ((a + 2) + (b + 2)))) ⋙
      RA a b ⋙ (JA2 a b).inverse :=
  DGModuleCat.tensorFunctorIsoOfEquiv (gEquiv a b).symm (gEquiv_symm_op_smul a b) ≪≫
    (DGModuleCat.tensorFunctorCompIso (ZD a b) (TT a b)).symm ≪≫
    Functor.isoWhiskerLeft _ (DGModuleCat.tensorFunctorCompIso (ZNat a b) (ZZ a b)).symm

/-- **Ellis–Qi, Corollary 4.21, the restriction half on abelian categories** (components
`ONH_{a+2} ⊗ ONH_{b+2}`): `R ∘ J^A ≅ J^A ∘ Res^♮`, with `ONH^♮` the right ideal `P^a ONH_{a+b}`
(`ONHNat`, ERRATA [EQ] 24) and `Z^♮_{a,b}` with `OΛ_{a+b}` acting through `swapDG`. -/
def resIsoA :
    ((JA (a + 2 + b)).functor : _ ⥤ DGModuleCat.{0} (osymDG ((a + 2) + (b + 2)))) ⋙ RA a b ≅
      ResNatA a b ⋙ (JA2 a b).functor :=
  (Functor.rightUnitor _).symm ≪≫ Functor.isoWhiskerLeft _ (JA2 a b).counitIso.symm ≪≫
    (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (resNatIso a b).symm (JA2 a b).functor

/-! ### The restriction half on homotopy categories -/

/-- `Res^♮` on homotopy categories. -/
abbrev ResNatH : DG.HomotopyCategory.{0} (ONH (a + 2 + b)) ⥤ DG.HomotopyCategory.{0} (𝒪a ᵍ⊗[ℤ] 𝒪b) :=
  HomotopyCategory.tensorFunctor (𝒪a ᵍ⊗[ℤ] 𝒪b) (ONHNat a b)

/-- `R` on homotopy categories. -/
abbrev RH : DG.HomotopyCategory.{0} (osymDG ((a + 2) + (b + 2))) ⥤ DG.HomotopyCategory.{0} (Λa ᵍ⊗[ℤ] Λb) :=
  HomotopyCategory.tensorFunctor (Λa ᵍ⊗[ℤ] Λb) (ZNat a b)

/-- **Ellis–Qi, Corollary 4.21, the restriction half on homotopy categories**: `R ∘ J^H ≅ J^H ∘ Res^♮`. -/
def resIsoH :
    ((JH (a + 2 + b)).functor : _ ⥤ DG.HomotopyCategory.{0} (osymDG ((a + 2) + (b + 2)))) ⋙ RH a b ≅
      ResNatH a b ⋙ (JH2 a b).functor :=
  HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _) ≪≫
    HomotopyCategory.liftNatIso _ _ (resIsoA a b) ≪≫
    (HomotopyCategory.liftFunctorCompIso _ _ (HomotopyCategory.tensorFunctor_homotopic _ _)
      (HomotopyCategory.tensorFunctor_homotopic _ _)).symm

end RestrictionA

/-! ### Derived categories -/

section Derived

universe w₁ w₂

variable (a b : ℕ)

local notation "𝒪a" => DGAlgebra.gradingSubmodule ℤ (ONH a)
local notation "𝒪b" => DGAlgebra.gradingSubmodule ℤ (ONH b)
local notation "Λa" => DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2))
local notation "Λb" => DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))

variable
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (DGAlgebra.gradingSubmodule ℤ (ONH a) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (ONH b)))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (ONH (a + 2 + b)))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2)) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2))))]
  [CatModule.HasDerivedCategory.{w₁, 0} (SingleObj (osymDG ((a + 2) + (b + 2))))]
  [DG.HasDerivedCategory.{w₂, 0} (DGAlgebra.gradingSubmodule ℤ (ONH a) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (ONH b))]
  [DG.HasDerivedCategory.{w₂, 0} (ONH (a + 2 + b))]
  [DG.HasDerivedCategory.{w₂, 0} (DGAlgebra.gradingSubmodule ℤ (osymDG (a + 2)) ᵍ⊗[ℤ]
    DGAlgebra.gradingSubmodule ℤ (osymDG (b + 2)))]
  [DG.HasDerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2)))]

/-- `R = Z^♮_{a,b} ⊗^L_{OΛ_{a+b}} (-)`, derived induction along `swapDG`. -/
abbrev RD : DG.DerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2))) ⥤ DG.DerivedCategory.{w₂, 0} (Λa ᵍ⊗[ℤ] Λb) :=
  (swapDG a b).derivedInduction.{w₁, w₁, w₂, w₂}

/-- **Ellis–Qi, Corollary 4.21, the restriction half on derived categories**: `R ∘ J ≅ J ∘ Res^♮` for
every functor `Res^♮ : D(ONH_{a+b}) ⥤ D(ONH_a ⊗ ONH_b)` (in particular for `ONH^♮ ⊗^L (-)`), since both
`D(ONH_{a+b})` and `D(ONH_a ⊗ ONH_b)` are zero. -/
def resIsoD (F : DG.DerivedCategory.{w₂, 0} (ONH (a + 2 + b)) ⥤ DG.DerivedCategory.{w₂, 0} (𝒪a ᵍ⊗[ℤ] 𝒪b)) :
    (J.{w₁, w₁, w₂, w₂} (a + 2 + b) : _ ⥤ DG.DerivedCategory.{w₂, 0} (osymDG ((a + 2) + (b + 2)))) ⋙
        RD.{w₁, w₂} a b ≅
      F ⋙ J2D.{w₁, w₂} a b :=
  NatIso.ofComponents (fun X =>
    ((RD a b).map_isZero ((J (a + 2 + b)).map_isZero (EQOnhDG.ONH.isZero_derivedCategory _))).iso
      ((J2D a b).map_isZero (onhTensor_isZero_derivedCategory a b (F.obj X))))
    (fun _ => ((J2D a b).map_isZero (onhTensor_isZero_derivedCategory a b _)).eq_of_tgt _ _)

end Derived

end OddMath.Frontier.EQFunctor

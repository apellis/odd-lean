import OddMath.Frontier.EQQuantumGroups
import DG.HalfGraded.Field

/-!
# Assembling a twisted-bialgebra isomorphism `U⁺ ≅ ⨁_n M_n`

Algebraic bookkeeping for Ellis–Qi, arXiv:1504.01712v2, Theorem 4.17. Let `M_n` (`n ∈ ℕ`) be
`ℤ[√−1]`-modules, free of rank one with trivializations `e_n : M_n ≃ ℤ[√−1]`, and `ε_n ∈ M_n` with
`e_n(ε_n) = (√−1)^{-binom(n,2)}`. Then:

* `equiv e ε hε : U⁺ ≃ₗ[ℤ[√−1]] ⨁_n M_n`, `E^{(n)} ↦ ε_n` (`equiv_E`);
* for maps `mult a b : M_a ⊗ M_b → M_{a+b}` with `ε_a ⊗ ε_b ↦ [a+b, a]_{√−1} ε_{a+b}`, the induced
  bilinear map `mulMap mult` on `⨁_n M_n` satisfies `equiv (x y) = mulMap mult (equiv x) (equiv y)`
  (`equiv_mul`);
* for maps `comult a b n h : M_n → M_a ⊗ M_b` (`h : a + b = n`) with
  `ε_n ↦ (-√−1)^{ab} ε_a ⊗ ε_b`, the induced `comulMap comult : ⨁_n M_n → (⨁_n M_n) ⊗ (⨁_n M_n)`
  satisfies `comulMap comult (equiv x) = (equiv ⊗ equiv)(r x)`, with `r = EQQuantum.rU` the coproduct
  (2.2) for the twist `−1` (`equiv_comul`).
-/

noncomputable section

open TensorProduct Finset DirectSum

namespace OddMath.Frontier.EQK0.Assembly

open OddMath.Frontier.QuantumSl2Plus (qBinom)
open OddMath.Frontier.EQQuantum (UPlus evI rU)

variable {M : ℕ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, Module GaussianInt (M n)]
  (e : ∀ n, M n ≃ₗ[GaussianInt] GaussianInt) (ε : ∀ n, M n)
  (hε : ∀ n, e n (ε n) =
    ((DG.HalfGradedDGRing.GaussianQuot.unitI ^ (-(n.choose 2 : ℤ)) : GaussianIntˣ) : GaussianInt))

/-- The coordinate `M_n → ℤ[√−1]` dual to `ε_n`. -/
def coord (n : ℕ) : M n →ₗ[GaussianInt] GaussianInt :=
  ((DG.HalfGradedDGRing.GaussianQuot.unitI ^ ((n.choose 2 : ℕ) : ℤ) : GaussianIntˣ) : GaussianInt) •
    (e n).toLinearMap

include hε in
theorem coord_ε (n : ℕ) : coord e n (ε n) = 1 := by
  rw [coord, LinearMap.smul_apply, LinearEquiv.coe_coe, hε, smul_eq_mul, ← Units.val_mul, ← zpow_add,
    add_neg_cancel, zpow_zero, Units.val_one]

include hε in
theorem coord_smul_ε (n : ℕ) (s : M n) : coord e n s • ε n = s := by
  apply (e n).injective
  rw [LinearEquiv.map_smul, hε, coord, LinearMap.smul_apply, LinearEquiv.coe_coe, smul_eq_mul,
    smul_eq_mul, mul_comm, ← mul_assoc, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero,
    Units.val_one, one_mul]

/-- `U⁺ → ⨁_n M_n`, `E^{(n)} ↦ ε_n`. -/
def toSum : UPlus →ₗ[GaussianInt] ⨁ n, M n :=
  (EQQuantum.DP.basis evI).constr GaussianInt fun n => lof GaussianInt ℕ M n (ε n)

theorem toSum_E (n : ℕ) : toSum ε (EQQuantum.DP.E evI n) = lof GaussianInt ℕ M n (ε n) := by
  rw [← EQQuantum.DP.basis_apply, toSum, Module.Basis.constr_basis]

/-- `⨁_n M_n → U⁺`. -/
def ofSum : (⨁ n, M n) →ₗ[GaussianInt] UPlus :=
  toModule GaussianInt ℕ UPlus fun n =>
    (LinearMap.toSpanSingleton GaussianInt UPlus (EQQuantum.DP.E evI n)) ∘ₗ coord e n

theorem ofSum_lof (n : ℕ) (s : M n) :
    ofSum e (lof GaussianInt ℕ M n s) = coord e n s • EQQuantum.DP.E evI n := by
  rw [ofSum, toModule_lof, LinearMap.comp_apply, LinearMap.toSpanSingleton_apply]

/-- **`U⁺ ≃ ⨁_n M_n`**, `E^{(n)} ↦ ε_n`. -/
def equiv : UPlus ≃ₗ[GaussianInt] ⨁ n, M n :=
  LinearEquiv.ofLinearMap (toSum ε) (ofSum e)
    (linearMap_ext GaussianInt fun n => LinearMap.ext fun s => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply, ofSum_lof, LinearMap.map_smul, toSum_E,
        ← LinearMap.map_smul, coord_smul_ε e ε hε, LinearMap.id_comp])
    ((EQQuantum.DP.basis evI).ext fun n => by
      rw [LinearMap.comp_apply, EQQuantum.DP.basis_apply, toSum_E, ofSum_lof, coord_ε e ε hε,
        one_smul, LinearMap.id_apply])

theorem equiv_E (n : ℕ) : equiv e ε hε (EQQuantum.DP.E evI n) = lof GaussianInt ℕ M n (ε n) :=
  toSum_E ε n

/-! ### Multiplication -/

/-- The bilinear map on `⨁_n M_n` with components `mult a b`. -/
def mulMap (mult : ∀ a b, M a ⊗[GaussianInt] M b →ₗ[GaussianInt] M (a+b)) :
    (⨁ n, M n) →ₗ[GaussianInt] (⨁ n, M n) →ₗ[GaussianInt] ⨁ n, M n :=
  toModule GaussianInt ℕ _ fun a =>
    (toModule GaussianInt ℕ _ fun b =>
      ((TensorProduct.mk GaussianInt (M a) (M b)).compr₂
        ((lof GaussianInt ℕ M (a+b)) ∘ₗ mult a b)).flip).flip

theorem mulMap_lof (mult : ∀ a b, M a ⊗[GaussianInt] M b →ₗ[GaussianInt] M (a+b)) (a b : ℕ)
    (x : M a) (y : M b) :
    mulMap mult (lof GaussianInt ℕ M a x) (lof GaussianInt ℕ M b y) =
      lof GaussianInt ℕ M (a+b) (mult a b (x ⊗ₜ y)) := by
  rw [mulMap, toModule_lof, LinearMap.flip_apply, toModule_lof, LinearMap.flip_apply,
    LinearMap.compr₂_apply, TensorProduct.mk_apply, LinearMap.comp_apply]

theorem equiv_mul (mult : ∀ a b, M a ⊗[GaussianInt] M b →ₗ[GaussianInt] M (a+b))
    (hmult : ∀ a b, mult a b (ε a ⊗ₜ ε b) = evI (qBinom a b) • ε (a+b)) (x y : UPlus) :
    equiv e ε hε (x * y) = mulMap mult (equiv e ε hε x) (equiv e ε hε y) := by
  have h : (LinearMap.mul GaussianInt UPlus).compr₂ (equiv e ε hε).toLinearMap =
      ((mulMap mult).comp (equiv e ε hε).toLinearMap).compl₂ (equiv e ε hε).toLinearMap := by
    refine LinearMap.ext_basis (EQQuantum.DP.basis evI) (EQQuantum.DP.basis evI) fun a b => ?_
    rw [LinearMap.compr₂_apply, LinearMap.mul_apply', LinearMap.compl₂_apply, LinearMap.comp_apply,
      EQQuantum.DP.basis_apply, EQQuantum.DP.basis_apply, LinearEquiv.coe_coe, EQQuantum.DP.E_mul_E, LinearEquiv.map_smul, equiv_E, equiv_E, equiv_E,
      mulMap_lof, hmult, LinearMap.map_smul]
  exact congrArg (fun f => f x y) h

/-! ### Comultiplication -/

/-- The map `⨁_n M_n → (⨁_n M_n) ⊗ (⨁_n M_n)` with components `Σ_{a+b=n} comult a b n`. -/
def comulMap (comult : ∀ a b n, a + b = n → (M n →ₗ[GaussianInt] M a ⊗[GaussianInt] M b)) :
    (⨁ n, M n) →ₗ[GaussianInt] (⨁ n, M n) ⊗[GaussianInt] (⨁ n, M n) :=
  toModule GaussianInt ℕ _ fun n =>
    ∑ p ∈ (antidiagonal n).attach,
      (TensorProduct.map (lof GaussianInt ℕ M p.1.1) (lof GaussianInt ℕ M p.1.2)) ∘ₗ
        comult p.1.1 p.1.2 n (mem_antidiagonal.mp p.2)

theorem equiv_comul (comult : ∀ a b n, a + b = n → (M n →ₗ[GaussianInt] M a ⊗[GaussianInt] M b))
    (hcomult : ∀ a b n (h : a + b = n),
      comult a b n h (ε n) = ((-EQQuantum.ii) ^ (a * b) : GaussianInt) • (ε a ⊗ₜ ε b))
    (x : UPlus) :
    comulMap comult (equiv e ε hε x) =
      TensorProduct.map (equiv e ε hε).toLinearMap (equiv e ε hε).toLinearMap
        (EQQuantum.TT.tensorEquiv evI (-1) (rU x)) := by
  have h : (comulMap comult).comp (equiv e ε hε).toLinearMap =
      (TensorProduct.map (equiv e ε hε).toLinearMap (equiv e ε hε).toLinearMap) ∘ₗ
        (EQQuantum.TT.tensorEquiv evI (-1)).toLinearMap ∘ₗ rU.toLinearMap := by
    refine (EQQuantum.DP.basis evI).ext fun n => ?_
    let g : ℕ × ℕ → (⨁ n, M n) ⊗[GaussianInt] (⨁ n, M n) := fun p =>
      ((-EQQuantum.ii) ^ (p.1 * p.2) : GaussianInt) •
        (lof GaussianInt ℕ M p.1 (ε p.1) ⊗ₜ[GaussianInt] lof GaussianInt ℕ M p.2 (ε p.2))
    have hL : comulMap comult (lof GaussianInt ℕ M n (ε n)) = ∑ c ∈ range (n + 1), g (c, n - c) := by
      rw [comulMap, toModule_lof, LinearMap.sum_apply]
      refine (Finset.sum_congr rfl fun p _ => ?_).trans
        ((Finset.sum_attach (antidiagonal n) g).trans
          (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk g n))
      rw [LinearMap.comp_apply, hcomult, LinearMap.map_smul, TensorProduct.map_tmul]
    have hR : TensorProduct.map (equiv e ε hε).toLinearMap (equiv e ε hε).toLinearMap
        (EQQuantum.TT.tensorEquiv evI (-1) (rU (EQQuantum.DP.E evI n))) =
        ∑ c ∈ range (n + 1), g (c, n - c) := by
      rw [EQQuantum.eq_2_2, map_sum, map_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [LinearEquiv.map_smul, LinearMap.map_smul, EQQuantum.TT.tensorEquiv_tw,
        TensorProduct.map_tmul, LinearEquiv.coe_coe, equiv_E, equiv_E]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, EQQuantum.DP.basis_apply,
      LinearEquiv.coe_coe, equiv_E, AlgHom.toLinearMap_apply, LinearEquiv.coe_coe]
    exact hL.trans hR.symm
  exact congrArg (fun f => f x) h

end OddMath.Frontier.EQK0.Assembly

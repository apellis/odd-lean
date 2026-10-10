import OddMath.Frontier.EQK0Assembly

/-!
# Assembling a twisted-bialgebra isomorphism `u⁺ ≅ ⨁_n M_n`

Algebraic bookkeeping for Ellis–Qi, arXiv:1504.01712v2, Theorem 3.18 (the analogue of
`OddMath.Frontier.EQK0.Assembly` for `u⁺ = ℤ[√−1][E]/(E²)`). Let `M_n` (`n ∈ ℕ`) be
`ℤ[√−1]`-modules with `M_0`, `M_1` free of rank one, trivialized by `e_0`, `e_1` with
`e_0(ε_0) = e_1(ε_1) = 1`, and `M_n = 0` for `n ≥ 2`. Then:

* `equiv : u⁺ ≃ₗ[ℤ[√−1]] ⨁_n M_n`, `1 ↦ ε_0`, `E ↦ ε_1` (`equiv_one`, `equiv_eps`);
* for maps `mult a b : M_a ⊗ M_b → M_{a+b}` with `ε_a ⊗ ε_b ↦ ε_{a+b}` for `a + b ≤ 1`, the induced
  bilinear map `Assembly.mulMap mult` satisfies `equiv (x y) = mulMap mult (equiv x) (equiv y)`
  (`equiv_mul`; the component `(1, 1)` lands in `M_2 = 0`, matching `E² = 0`);
* `ruT : u⁺ → u⁺ ⊗ u⁺`, `1 ↦ 1 ⊗ 1`, `E ↦ E ⊗ 1 + 1 ⊗ E`, is the coproduct `EQQuantum.ru` of `u⁺`
  (twist `−1`) read in `u⁺ ⊗_{ℤ[√−1]} u⁺` (`tensorIota_ruT`); for maps
  `comult a b n h : M_n → M_a ⊗ M_b` with `ε_n ↦ ε_a ⊗ ε_b` for `n ≤ 1`, the induced
  `Assembly.comulMap comult` satisfies `comulMap comult (equiv x) = (equiv ⊗ equiv)(ruT x)`
  (`equiv_comul`).
-/

noncomputable section

open TensorProduct Finset DirectSum
open scoped DualNumber

namespace OddMath.Frontier.EQK0.AssemblySmall

open OddMath.Frontier.EQQuantum (uPlus iota ru tensorIota)

/-- `x = x₀ · 1 + x₁ · E` in `u⁺`. -/
theorem uPlus_decomp (x : uPlus) : x = x.fst • (1 : uPlus) + x.snd • ε := by
  ext <;> simp

/-! ### The coproduct of `u⁺` in `u⁺ ⊗ u⁺` -/

/-- `r : u⁺ → u⁺ ⊗ u⁺`, `1 ↦ 1 ⊗ 1`, `E ↦ E ⊗ 1 + 1 ⊗ E`. -/
def ruT : uPlus →ₗ[GaussianInt] uPlus ⊗[GaussianInt] uPlus where
  toFun x := x.fst • ((1 : uPlus) ⊗ₜ (1 : uPlus)) + x.snd • ((ε : uPlus) ⊗ₜ (1 : uPlus) + 1 ⊗ₜ ε)
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul]
    abel
  map_smul' c x := by
    simp only [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul, mul_smul,
      RingHom.id_apply, smul_add]

theorem ruT_one : ruT (1 : uPlus) = (1 : uPlus) ⊗ₜ (1 : uPlus) := by
  simp [ruT]

theorem ruT_eps : ruT (ε : uPlus) = (ε : uPlus) ⊗ₜ (1 : uPlus) + 1 ⊗ₜ ε := by
  simp [ruT]

/-- `ruT` is the coproduct `ru` of `u⁺` (twist `−1`), read through `u⁺ ⊗ u⁺ ↪ U⁺ ⊗ U⁺`. -/
theorem tensorIota_ruT (x : uPlus) : tensorIota (-1) (ruT x) = (ru x : EQQuantum.UPlusTensor (-1)) := by
  rw [uPlus_decomp x]
  simp only [map_add, map_smul, ruT_one, ruT_eps, map_one, Subalgebra.coe_add, Subalgebra.coe_smul,
    Subalgebra.coe_one, EQQuantum.ru_eps, EQQuantum.tensorIota_tmul, EQQuantum.iota_eps,
    ← EQQuantum.DP.E_zero, EQQuantum.TT.tmul_E, EQQuantum.TT.one_def]

/-! ### The isomorphism `u⁺ ≃ ⨁_n M_n` -/

variable {M : ℕ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, Module GaussianInt (M n)]
  (e0 : M 0 ≃ₗ[GaussianInt] GaussianInt) (e1 : M 1 ≃ₗ[GaussianInt] GaussianInt)
  (hz : ∀ n, Subsingleton (M (n+2))) (g : ∀ n, M n) (h0 : e0 (g 0) = 1) (h1 : e1 (g 1) = 1)

/-- `u⁺ → ⨁_n M_n`, `x₀ + x₁ E ↦ x₀ ε_0 + x₁ ε_1`. -/
def toSum : uPlus →ₗ[GaussianInt] ⨁ n, M n where
  toFun x := lof GaussianInt ℕ M 0 (x.fst • g 0) + lof GaussianInt ℕ M 1 (x.snd • g 1)
  map_add' x y := by
    simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, add_smul, map_add]
    abel
  map_smul' c x := by
    simp only [TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, smul_eq_mul, mul_smul, map_smul,
      RingHom.id_apply, smul_add]

/-- `⨁_n M_n → u⁺`. -/
def ofSum : (⨁ n, M n) →ₗ[GaussianInt] uPlus :=
  toModule GaussianInt ℕ uPlus fun n => match n with
    | 0 => Algebra.linearMap GaussianInt uPlus ∘ₗ e0.toLinearMap
    | 1 => TrivSqZeroExt.inrHom GaussianInt GaussianInt ∘ₗ e1.toLinearMap
    | _ + 2 => 0

include h0 in
theorem smul_g0 (m : M 0) : e0 m • g 0 = m :=
  e0.injective (by rw [map_smul, h0, smul_eq_mul, mul_one])

include h1 in
theorem smul_g1 (m : M 1) : e1 m • g 1 = m :=
  e1.injective (by rw [map_smul, h1, smul_eq_mul, mul_one])

/-- **`u⁺ ≃ ⨁_n M_n`**, `1 ↦ ε_0`, `E ↦ ε_1`. -/
def equiv : uPlus ≃ₗ[GaussianInt] ⨁ n, M n :=
  LinearEquiv.ofLinearMap (toSum g) (ofSum e0 e1)
    (linearMap_ext GaussianInt fun n => LinearMap.ext fun m => by
      match n with
      | 0 =>
        change toSum g (ofSum e0 e1 (lof GaussianInt ℕ M 0 m)) = lof GaussianInt ℕ M 0 m
        rw [ofSum, toModule_lof]
        change lof GaussianInt ℕ M 0 ((algebraMap GaussianInt uPlus (e0 m)).fst • g 0) +
          lof GaussianInt ℕ M 1 ((algebraMap GaussianInt uPlus (e0 m)).snd • g 1) = _
        rw [TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, zero_smul, map_zero, add_zero,
          smul_g0 e0 g h0]
      | 1 =>
        change toSum g (ofSum e0 e1 (lof GaussianInt ℕ M 1 m)) = lof GaussianInt ℕ M 1 m
        rw [ofSum, toModule_lof]
        change lof GaussianInt ℕ M 0 ((TrivSqZeroExt.inr (e1 m) : uPlus).fst • g 0) +
          lof GaussianInt ℕ M 1 ((TrivSqZeroExt.inr (e1 m) : uPlus).snd • g 1) = _
        rw [TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, zero_smul, map_zero, zero_add,
          smul_g1 e1 g h1]
      | k + 2 =>
        change toSum g (ofSum e0 e1 (lof GaussianInt ℕ M (k+2) m)) = lof GaussianInt ℕ M (k+2) m
        rw [(hz k).elim m 0, map_zero, map_zero, map_zero])
    (LinearMap.ext fun x => by
      change ofSum e0 e1 (lof GaussianInt ℕ M 0 (x.fst • g 0) + lof GaussianInt ℕ M 1 (x.snd • g 1))
        = x
      rw [map_add, ofSum, toModule_lof, toModule_lof]
      change algebraMap GaussianInt uPlus (e0 (x.fst • g 0)) + TrivSqZeroExt.inr (e1 (x.snd • g 1))
        = x
      rw [TrivSqZeroExt.algebraMap_eq_inl, map_smul, map_smul, h0, h1, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
        TrivSqZeroExt.inl_fst_add_inr_snd_eq])

theorem equiv_apply (x : uPlus) :
    equiv e0 e1 hz g h0 h1 x =
      lof GaussianInt ℕ M 0 (x.fst • g 0) + lof GaussianInt ℕ M 1 (x.snd • g 1) := rfl

theorem equiv_one : equiv e0 e1 hz g h0 h1 1 = lof GaussianInt ℕ M 0 (g 0) := by
  rw [equiv_apply, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, one_smul, zero_smul, map_zero,
    add_zero]

theorem equiv_eps : equiv e0 e1 hz g h0 h1 (ε : uPlus) = lof GaussianInt ℕ M 1 (g 1) := by
  rw [equiv_apply, DualNumber.fst_eps, DualNumber.snd_eps, one_smul, zero_smul, map_zero,
    zero_add]

/-! ### Multiplication -/

theorem equiv_mul (mult : ∀ a b, M a ⊗[GaussianInt] M b →ₗ[GaussianInt] M (a+b))
    (hm00 : mult 0 0 (g 0 ⊗ₜ g 0) = g 0) (hm01 : mult 0 1 (g 0 ⊗ₜ g 1) = g 1)
    (hm10 : mult 1 0 (g 1 ⊗ₜ g 0) = g 1) (x y : uPlus) :
    equiv e0 e1 hz g h0 h1 (x * y) =
      Assembly.mulMap mult (equiv e0 e1 hz g h0 h1 x) (equiv e0 e1 hz g h0 h1 y) := by
  have e00 : Assembly.mulMap mult (lof GaussianInt ℕ M 0 (g 0)) (lof GaussianInt ℕ M 0 (g 0)) =
      lof GaussianInt ℕ M 0 (g 0) := by
    rw [Assembly.mulMap_lof, hm00]
  have e01 : Assembly.mulMap mult (lof GaussianInt ℕ M 0 (g 0)) (lof GaussianInt ℕ M 1 (g 1)) =
      lof GaussianInt ℕ M 1 (g 1) := by
    rw [Assembly.mulMap_lof, hm01]
  have e10 : Assembly.mulMap mult (lof GaussianInt ℕ M 1 (g 1)) (lof GaussianInt ℕ M 0 (g 0)) =
      lof GaussianInt ℕ M 1 (g 1) := by
    rw [Assembly.mulMap_lof, hm10]
  have e11 : Assembly.mulMap mult (lof GaussianInt ℕ M 1 (g 1)) (lof GaussianInt ℕ M 1 (g 1)) = 0 := by
    rw [Assembly.mulMap_lof, @Subsingleton.elim (M (1+1)) (hz 0) (mult 1 1 _) 0, map_zero]
  have hxy : x * y = (x.fst * y.fst) • (1 : uPlus) + (x.fst * y.snd + x.snd * y.fst) • ε := by
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, mul_comm]
  rw [hxy, uPlus_decomp x, uPlus_decomp y]
  simp only [map_add, map_smul, equiv_one, equiv_eps, LinearMap.add_apply, LinearMap.smul_apply,
    e00, e01, e10, e11, smul_zero, add_zero, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one,
    DualNumber.fst_eps, DualNumber.snd_eps, smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
  module

/-! ### Comultiplication -/

theorem comulMap_lof (comult : ∀ a b n, a + b = n → (M n →ₗ[GaussianInt] M a ⊗[GaussianInt] M b))
    (hcomult : ∀ a b n (h : a + b = n), n ≤ 1 → comult a b n h (g n) = g a ⊗ₜ g b)
    {n : ℕ} (hn : n ≤ 1) :
    Assembly.comulMap comult (lof GaussianInt ℕ M n (g n)) =
      ∑ c ∈ range (n + 1), lof GaussianInt ℕ M c (g c) ⊗ₜ[GaussianInt]
        lof GaussianInt ℕ M (n - c) (g (n - c)) := by
  let g : ℕ × ℕ → (⨁ n, M n) ⊗[GaussianInt] (⨁ n, M n) := fun p =>
    lof GaussianInt ℕ M p.1 (g p.1) ⊗ₜ[GaussianInt] lof GaussianInt ℕ M p.2 (g p.2)
  rw [Assembly.comulMap, toModule_lof, LinearMap.sum_apply]
  refine (Finset.sum_congr rfl fun p _ => ?_).trans
    ((Finset.sum_attach (antidiagonal n) g).trans
      (Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk g n))
  rw [LinearMap.comp_apply, hcomult _ _ _ _ hn, TensorProduct.map_tmul]

theorem equiv_comul (comult : ∀ a b n, a + b = n → (M n →ₗ[GaussianInt] M a ⊗[GaussianInt] M b))
    (hcomult : ∀ a b n (h : a + b = n), n ≤ 1 → comult a b n h (g n) = g a ⊗ₜ g b) (x : uPlus) :
    Assembly.comulMap comult (equiv e0 e1 hz g h0 h1 x) =
      TensorProduct.map (equiv e0 e1 hz g h0 h1).toLinearMap (equiv e0 e1 hz g h0 h1).toLinearMap
        (ruT x) := by
  have c0 := comulMap_lof g comult hcomult (n := 0) (Nat.zero_le 1)
  have c1 := comulMap_lof g comult hcomult (n := 1) le_rfl
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at c0 c1
  rw [uPlus_decomp x]
  simp only [map_add, map_smul, equiv_one, equiv_eps, ruT_one, ruT_eps, TensorProduct.map_tmul,
    LinearEquiv.coe_coe]
  rw [c0, c1]
  change _ = x.fst • (lof GaussianInt ℕ M 0 (g 0) ⊗ₜ[GaussianInt] lof GaussianInt ℕ M 0 (g 0)) +
    x.snd • (lof GaussianInt ℕ M 1 (g 1) ⊗ₜ[GaussianInt] lof GaussianInt ℕ M 0 (g 0) +
      lof GaussianInt ℕ M 0 (g 0) ⊗ₜ[GaussianInt] lof GaussianInt ℕ M 1 (g 1))
  rw [add_comm (lof GaussianInt ℕ M 1 (g 1) ⊗ₜ[GaussianInt] _)]

end OddMath.Frontier.EQK0.AssemblySmall

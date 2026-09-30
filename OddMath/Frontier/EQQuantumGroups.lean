import OddMath.Frontier.EQQuantumBialgebra

/-!
# Quantum `sl₂` at a fourth root of unity (Ellis–Qi §2.1)

Ellis–Qi, *The differential graded odd nilHecke algebra*, arXiv:1504.01712v2, §2.1.

* `UPlus = U⁺_{√−1}(sl₂)`: the `ℤ[√−1]`-algebra with basis `E^{(n)}` and product (2.1),
  `E^{(a)}E^{(b)} = [a+b, a]_{q=√−1} E^{(a+b)}` (`eq_2_1`, `eq_2_1_explicit`). It is the
  specialisation of Lusztig's integral form `U_A` along `q ↦ √−1` (`mapDP evI`).
* `UPlusTensor t = U⁺ ⊗ U⁺` with the twisted product
  `(b₁ ⊗ b₂)(b₁' ⊗ b₂') = t^{|b₂||b₁'|} b₁b₁' ⊗ b₂b₂'`, `|E^{(n)}| = n` (`TT.tmul_mul_tmul`).
* **The printed convention is inconsistent.** The paper takes the twist `v^{|b₂||b₁'|}` with
  `v = √−1`. Then `r(E^{(1)})² = (1 + √−1) E^{(1)} ⊗ E^{(1)} ≠ 0` (`tw_sq`), whereas
  `E^{(1)}E^{(1)} = 0`; so the map `r` of (2.2) is not multiplicative (`printed_r_not_mul`), and in
  fact no algebra map `U⁺ → U⁺ ⊗ U⁺` with `r(E^{(1)}) = E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)}` exists
  (`printed_twist_no_coproduct`); the same holds for `u⁺` (`small_printed_twist_no_coproduct`).
* **Correction.** For both `u⁺` and `U⁺`, such a coproduct exists **iff the twist is
  `t = −1`**, i.e. `(b₁ ⊗ b₂)(b₁' ⊗ b₂') = (−1)^{|b₂||b₁'|} b₁b₁' ⊗ b₂b₂'`
  (`twisted_coproduct_exists_iff`, `small_twisted_coproduct_exists_iff`). This is Lusztig's
  convention `v^{(|b₂|, |b₁'|)}` with `(E, E) = 2` [Lus93, 1.2.2] at `v = √−1`, and it is the
  specialisation at `q = √−1` of the Ellis–Khovanov–Lauda `q`-bialgebra of the library
  (braiding `q^{-2}`, `evI_T_neg_two`, `rU_mapDP`). With this twist, (2.2) defines a coassociative
  counital algebra map `rU` (`eq_2_2`, `rU_coassoc`, `counitLeft_rU`, `counitRight_rU`).
* `uPlus = u⁺ = ℤ[√−1][E]/(E²)` (dual numbers); `iota : u⁺ → U⁺`, `E ↦ E^{(1)}`, is an injective
  algebra map (`iota_injective`), and `u⁺ ⊗ u⁺ ⊂ U⁺ ⊗ U⁺` is the subalgebra `uPlusTensor t`
  spanned by `E^{(a)} ⊗ E^{(b)}`, `a, b ≤ 1`, the image of the injective map
  `u⁺ ⊗_{ℤ[√−1]} u⁺ → U⁺ ⊗ U⁺` (`tensorIota_injective`, `range_tensorIota`). The coproduct
  `ru : u⁺ → u⁺ ⊗ u⁺` (twist `−1`) has `ru(E) = E ⊗ 1 + 1 ⊗ E` (`ru_eps`) and
  `rU ∘ iota = ru` (`rU_iota`): `u⁺ ↪ U⁺` is a homomorphism of twisted bialgebras.
-/

noncomputable section
open Finset LaurentPolynomial
open scoped TensorProduct DualNumber

namespace OddMath.Frontier.EQQuantum
open QuantumSl2Plus DP TT

local notation "A" => LaurentPolynomial ℤ

/-! ### `U⁺ = U⁺_{√−1}(sl₂)` -/

/-- `U⁺ = U⁺_{√−1}(sl₂)`: the `ℤ[√−1]`-algebra with basis `{E^{(n)}}` and product (2.1). -/
abbrev UPlus : Type := DP evI

/-- `U⁺ ⊗_{ℤ[√−1]} U⁺` with the twisted product of twist parameter `t`
(`(b₁ ⊗ b₂)(b₁' ⊗ b₂') = t^{|b₂||b₁'|} b₁b₁' ⊗ b₂b₂'`, `|E^{(n)}| = n`). -/
abbrev UPlusTensor (t : GaussianInt) : Type := TT evI t

/-- **(2.1)** `E^{(a)} E^{(b)} = [a+b, a]_{q=√−1} E^{(a+b)}`. -/
theorem eq_2_1 (a b : ℕ) : E evI a * E evI b = evI (qBinom a b) • E evI (a + b) := E_mul_E a b

/-- (2.1) with the structure constants made explicit:
`E^{(a)} E^{(b)} = (−√−1)^{ab} β(a, b) E^{(a+b)}`, `β(a, b) = 0` if `a, b` are both odd and
`C(⌊(a+b)/2⌋, ⌊a/2⌋)` otherwise. -/
theorem eq_2_1_explicit (a b : ℕ) :
    E evI a * E evI b = ((-ii) ^ (a * b) * (binomNegOne a b : GaussianInt)) • E evI (a + b) := by
  rw [eq_2_1, evI_qBinom]

/-- `E^{(a)} E^{(b)} = 0` iff `a` and `b` are both odd. -/
theorem E_mul_E_eq_zero_iff (a b : ℕ) : E evI a * E evI b = 0 ↔ Odd a ∧ Odd b := by
  rw [eq_2_1, ← evI_qBinom_eq_zero_iff]
  constructor
  · intro h
    have := congrArg (DP.coeff evI (a + b)) h
    rw [map_smul, map_zero, DP.coeff_E, ite_eq_left rfl, smul_eq_mul, mul_one] at this
    exact this
  · intro h
    rw [h, zero_smul]

/-- `E^{(1)} E^{(1)} = (√−1 + (√−1)⁻¹) E^{(2)} = 0`. -/
theorem E_one_mul_E_one : E evI 1 * E evI 1 = 0 := by
  rw [eq_2_1, evI_qBinom_one_one, zero_smul]

/-! ### The corrected coproduct on `U⁺` -/

/-- **The coproduct (2.2)** `r : U⁺ → U⁺ ⊗ U⁺`, an algebra map for the twisted product with
twist `−1` (the specialisation at `q = √−1` of the library's `OddBialgebra.coprod`). -/
def rU : UPlus →ₐ[GaussianInt] UPlusTensor (-1) := r evI evI_T_neg_two

/-- **(2.2)** `r(E^{(a)}) = ∑_{c=0}^{a} (−√−1)^{c(a−c)} E^{(c)} ⊗ E^{(a−c)}`. -/
theorem eq_2_2 (a : ℕ) :
    rU (E evI a) = ∑ c ∈ range (a + 1), (-ii) ^ (c * (a - c)) • tw evI (-1) c (a - c) := by
  rw [rU, r_E, rVal, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun c _ => ?_
  rw [evI_T_neg_nat]

theorem rU_E_one : rU (E evI 1) = tw evI (-1) 1 0 + tw evI (-1) 0 1 := by
  rw [rU, r_E, rVal_one]

/-- `rU` is the specialisation at `q = √−1` of the EKL coproduct `OddBialgebra.coprod` on `U_A`
(braiding `q^{-2}`). -/
theorem rU_mapDP (x : DivPowAlg) :
    rU (mapDP evI x) = mapTT evI (T (-2)) evI_T_neg_two (OddBialgebra.coprod x) :=
  r_mapDP evI evI_T_neg_two x

theorem mapDP_evI_θ (a : ℕ) : mapDP evI (DivPowAlg.θ a) = E evI a := mapDP_θ evI a

/-- Coassociativity of `rU`. -/
theorem rU_coassoc (x : UPlus) : rLeft evI (-1) (rU x) = rRight evI (-1) (rU x) :=
  coassoc evI evI_T_neg_two x

/-- Counit laws for `rU`. -/
theorem counitLeft_rU (x : UPlus) : counitLeft evI (-1) (rU x) = x :=
  counitLeft_r evI evI_T_neg_two x

theorem counitRight_rU (x : UPlus) : counitRight evI (-1) (rU x) = x :=
  counitRight_r evI evI_T_neg_two x

/-! ### The printed twist `v = √−1` -/

/-- In `U⁺ ⊗ U⁺` with twist `t`: `(E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)})² = (1 + t) E^{(1)} ⊗ E^{(1)}`. -/
theorem tw_sq (t : GaussianInt) :
    (tw evI t 1 0 + tw evI t 0 1) ^ 2 = (1 + t) • tw evI t 1 1 := by
  simp only [pow_two, add_mul, mul_add, tw_mul_tw, TT.coeff, evI_qBinom_one_one, qBinom_zero_left,
    qBinom_zero_right, map_one]
  simp only [mul_zero, zero_smul, zero_add, add_zero, mul_one, pow_zero,
    pow_one, add_smul, one_smul]
  abel

theorem tw_one_one_ne_zero (t : GaussianInt) : tw evI t 1 1 ≠ 0 := by
  intro h
  have := congrArg (coeffAt evI t (1, 1)) h
  rw [coeffAt_tw, ite_eq_left rfl, map_zero] at this
  exact one_ne_zero this

theorem one_add_ii_ne_zero : (1 + ii : GaussianInt) ≠ 0 := by decide

/-- The linear map `U⁺ → U⁺ ⊗ U⁺` defined by (2.2), with values in `U⁺ ⊗ U⁺` carrying the
twist `t`. -/
def rLin (t : GaussianInt) : UPlus →ₗ[GaussianInt] UPlusTensor t :=
  (DP.basis evI).constr GaussianInt fun a =>
    ∑ c ∈ range (a + 1), (-ii) ^ (c * (a - c)) • tw evI t c (a - c)

theorem rLin_E_one (t : GaussianInt) : rLin t (E evI 1) = tw evI t 1 0 + tw evI t 0 1 := by
  rw [rLin, ← DP.basis_apply, Module.Basis.constr_basis]
  simp [sum_range_succ, add_comm]

/-- **The printed convention fails.** With the twist `v^{|b₂||b₁'|}`, `v = √−1`, as printed in
§2.1, the map `r` of (2.2) is not multiplicative:
`r(E^{(1)}E^{(1)}) = r(0) = 0` but `r(E^{(1)})² = (1 + √−1) E^{(1)} ⊗ E^{(1)} ≠ 0`. -/
theorem printed_r_not_mul : ¬ ∀ x y : UPlus, rLin ii (x * y) = rLin ii x * rLin ii y := by
  intro h
  have h1 := h (E evI 1) (E evI 1)
  rw [E_one_mul_E_one, map_zero, rLin_E_one, ← pow_two, tw_sq] at h1
  exact smul_tw_ne_zero one_add_ii_ne_zero 1 1 h1.symm

/-- **The printed convention fails (strong form).** For the twist `√−1` there is no algebra map
`U⁺ → U⁺ ⊗ U⁺` at all with `E^{(1)} ↦ E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)}`. -/
theorem printed_twist_no_coproduct :
    ¬ ∃ f : UPlus →ₐ[GaussianInt] UPlusTensor ii, f (E evI 1) = tw evI ii 1 0 + tw evI ii 0 1 := by
  rintro ⟨f, hf⟩
  have := twist_eq_neg_one_of_sq_zero evI evI_qBinom_one_one f hf
  exact absurd this (by decide)

/-- **The corrected convention.** An algebra map `r : U⁺ → U⁺ ⊗ U⁺` (twisted product with twist
parameter `t`) with `r(E^{(1)}) = E^{(1)} ⊗ 1 + 1 ⊗ E^{(1)}` exists iff `t = −1`. For `t = −1`,
(2.2) gives one (`rU`). -/
theorem twisted_coproduct_exists_iff (t : GaussianInt) :
    (∃ f : UPlus →ₐ[GaussianInt] UPlusTensor t, f (E evI 1) = tw evI t 1 0 + tw evI t 0 1) ↔
      t = -1 := by
  constructor
  · rintro ⟨f, hf⟩
    exact twist_eq_neg_one_of_sq_zero evI evI_qBinom_one_one f hf
  · rintro rfl
    exact ⟨rU, rU_E_one⟩

/-! ### `u⁺ = ℤ[√−1][E]/(E²)` and `u⁺ ↪ U⁺` -/

/-- `u⁺ = u⁺_{√−1}(sl₂) = ℤ[√−1][E]/(E²)` (the dual numbers over `ℤ[√−1]`, `E = ε`). -/
abbrev uPlus : Type := DualNumber GaussianInt

/-- `u⁺ = ℤ[√−1] ⊕ ℤ[√−1] E` is a free `ℤ[√−1]`-module. -/
instance uPlus.instFree : Module.Free GaussianInt uPlus :=
  inferInstanceAs (Module.Free GaussianInt (GaussianInt × GaussianInt))

/-- `u⁺ ↪ U⁺`, `E ↦ E^{(1)}` (an algebra map since `E^{(1)}E^{(1)} = 0`). -/
def iota : uPlus →ₐ[GaussianInt] UPlus :=
  DualNumber.lift ⟨(Algebra.ofId GaussianInt UPlus, E evI 1), E_one_mul_E_one,
    fun a => (Algebra.commutes a (E evI 1)).symm⟩

theorem iota_apply (x : uPlus) :
    iota x = DP.single evI 0 x.fst + DP.single evI 1 x.snd := by
  rw [iota, DualNumber.lift_apply_apply]
  simp only [Algebra.ofId_apply]
  rw [Algebra.algebraMap_eq_smul_one, ← Algebra.smul_def, DP.one_def, ← DP.single_eq_smul,
    ← DP.single_eq_smul]

theorem iota_eps : iota ε = E evI 1 := by
  rw [iota_apply, DualNumber.fst_eps, DualNumber.snd_eps]
  simp only [DP.single, Finsupp.single_zero, zero_add]
  rfl

theorem iota_injective : Function.Injective iota := by
  intro x y h
  rw [iota_apply, iota_apply] at h
  have h0 := congrArg (DP.coeff evI 0) h
  have h1 := congrArg (DP.coeff evI 1) h
  simp only [map_add, DP.coeff_single] at h0 h1
  simp at h0 h1
  exact TrivSqZeroExt.ext h0 h1

/-- For every twist `t`, the `ℤ[√−1]`-span of `E^{(a)} ⊗ E^{(b)}`, `a, b ≤ 1`, in `U⁺ ⊗ U⁺`. -/
def uPlusTensorSpan (t : GaussianInt) : Submodule GaussianInt (UPlusTensor t) :=
  Submodule.span GaussianInt {x | ∃ a b : ℕ, a ≤ 1 ∧ b ≤ 1 ∧ x = tw evI t a b}

theorem tw_mem_span {t : GaussianInt} {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) :
    tw evI t a b ∈ uPlusTensorSpan t :=
  Submodule.subset_span ⟨a, b, ha, hb, rfl⟩

theorem tw_mul_tw_mem_span {t : GaussianInt} {a b c d : ℕ} (ha : a ≤ 1) (hb : b ≤ 1) (hc : c ≤ 1)
    (hd : d ≤ 1) : tw evI t a b * tw evI t c d ∈ uPlusTensorSpan t := by
  rw [tw_mul_tw]
  by_cases hac : a + c ≤ 1
  · by_cases hbd : b + d ≤ 1
    · exact Submodule.smul_mem _ _ (tw_mem_span hac hbd)
    · obtain ⟨rfl, rfl⟩ : b = 1 ∧ d = 1 := by omega
      rw [TT.coeff, evI_qBinom_one_one, mul_zero, zero_smul]
      exact zero_mem _
  · obtain ⟨rfl, rfl⟩ : a = 1 ∧ c = 1 := by omega
    rw [TT.coeff, evI_qBinom_one_one, mul_zero, zero_mul, zero_smul]
    exact zero_mem _

/-- `u⁺ ⊗ u⁺ ⊂ U⁺ ⊗ U⁺` with the twisted product: the subalgebra spanned by `E^{(a)} ⊗ E^{(b)}`,
`a, b ≤ 1` (closed under the product since `E^{(1)}E^{(1)} = 0`). -/
def uPlusTensor (t : GaussianInt) : Subalgebra GaussianInt (UPlusTensor t) :=
  (uPlusTensorSpan t).toSubalgebra (tw_mem_span (Nat.zero_le 1) (Nat.zero_le 1)) fun x y hx hy => by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, b, ha, hb, rfl⟩ := hx
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, d, hc, hd, rfl⟩ := hy
        exact tw_mul_tw_mem_span ha hb hc hd
      | zero => rw [mul_zero]; exact zero_mem _
      | add y y' _ _ h h' => rw [mul_add]; exact add_mem h h'
      | smul c y _ h => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ h
    | zero => rw [zero_mul]; exact zero_mem _
    | add x x' _ _ h h' => rw [add_mul]; exact add_mem h h'
    | smul c x _ h => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ h

/-- The injective map `u⁺ ⊗_{ℤ[√−1]} u⁺ → U⁺ ⊗ U⁺`, `x ⊗ y ↦ ι(x) ⊗ ι(y)`. -/
def tensorIota (t : GaussianInt) : uPlus ⊗[GaussianInt] uPlus →ₗ[GaussianInt] UPlusTensor t :=
  (TT.tensorEquiv evI t).symm.toLinearMap ∘ₗ TensorProduct.map iota.toLinearMap iota.toLinearMap

theorem tensorIota_injective (t : GaussianInt) : Function.Injective (tensorIota t) := by
  rw [tensorIota, LinearMap.coe_comp]
  exact (TT.tensorEquiv evI t).symm.injective.comp
    (TensorProduct.map_injective_of_flat_flat _ _ iota_injective iota_injective)

theorem tensorIota_tmul (t : GaussianInt) (x y : uPlus) :
    tensorIota t (x ⊗ₜ y) = TT.tmul evI t (iota x) (iota y) := rfl

/-- The image of `u⁺ ⊗ u⁺` in `U⁺ ⊗ U⁺` is `uPlusTensor t`. -/
theorem range_tensorIota (t : GaussianInt) :
    LinearMap.range (tensorIota t) = Subalgebra.toSubmodule (uPlusTensor t) := by
  have hE : ∀ a : ℕ, a ≤ 1 → ∃ x : uPlus, iota x = E evI a := by
    intro a ha
    interval_cases a
    · exact ⟨1, map_one _⟩
    · exact ⟨ε, iota_eps⟩
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | add z z' h h' => rw [map_add]; exact add_mem h h'
    | tmul x y =>
      rw [tensorIota_tmul, iota_apply, iota_apply]
      simp only [DP.single_eq_smul, TT.tmul_add_left, TT.tmul_add_right, TT.tmul_smul_left,
        TT.tmul_smul_right, TT.tmul_E]
      show _ ∈ uPlusTensorSpan t
      repeat' first
        | exact tw_mem_span (by norm_num) (by norm_num)
        | apply add_mem
        | apply Submodule.smul_mem
  · show uPlusTensorSpan t ≤ _
    rw [uPlusTensorSpan, Submodule.span_le]
    rintro _ ⟨a, b, ha, hb, rfl⟩
    obtain ⟨x, hx⟩ := hE a ha
    obtain ⟨y, hy⟩ := hE b hb
    exact ⟨x ⊗ₜ y, by rw [tensorIota_tmul, hx, hy, TT.tmul_E]⟩

/-! ### The coproduct on `u⁺` -/

theorem rU_iota_mem (x : uPlus) : rU (iota x) ∈ uPlusTensor (-1) := by
  rw [iota_apply, DP.single_eq_smul, DP.single_eq_smul, map_add, map_smul, map_smul, E_zero,
    map_one, rU_E_one]
  refine add_mem (Subalgebra.smul_mem _ (one_mem _) _) (Subalgebra.smul_mem _ (add_mem ?_ ?_) _)
  · exact tw_mem_span le_rfl (Nat.zero_le 1)
  · exact tw_mem_span (Nat.zero_le 1) le_rfl

/-- **The coproduct of `u⁺`**, `r : u⁺ → u⁺ ⊗ u⁺` (twist `−1`), the restriction of `rU`. -/
def ru : uPlus →ₐ[GaussianInt] uPlusTensor (-1) := (rU.comp iota).codRestrict _ rU_iota_mem

/-- `r(E) = E ⊗ 1 + 1 ⊗ E`. -/
theorem ru_eps : (ru ε : UPlusTensor (-1)) = tw evI (-1) 1 0 + tw evI (-1) 0 1 := by
  show rU (iota ε) = _
  rw [iota_eps, rU_E_one]

/-- **`u⁺ ↪ U⁺` is a homomorphism of twisted bialgebras**: `rU ∘ ι = (ι ⊗ ι) ∘ ru`, where
`u⁺ ⊗ u⁺ ⊂ U⁺ ⊗ U⁺` is `uPlusTensor (−1)`. -/
theorem rU_iota (x : uPlus) : rU (iota x) = ru x := rfl

/-- **The printed convention fails for `u⁺`.** With twist `√−1` there is no algebra map
`u⁺ → U⁺ ⊗ U⁺` (a fortiori none into `u⁺ ⊗ u⁺`) with `E ↦ E ⊗ 1 + 1 ⊗ E`:
`r(E)² = (1 + √−1) E ⊗ E ≠ 0 = r(E²)`. -/
theorem small_printed_twist_no_coproduct :
    ¬ ∃ f : uPlus →ₐ[GaussianInt] UPlusTensor ii, f ε = tw evI ii 1 0 + tw evI ii 0 1 := by
  rintro ⟨f, hf⟩
  have h := congrArg f (DualNumber.eps_mul_eps (R := GaussianInt))
  rw [map_mul, map_zero, hf, ← pow_two, tw_sq] at h
  exact smul_tw_ne_zero one_add_ii_ne_zero 1 1 h

/-- **The corrected convention for `u⁺`.** An algebra map `u⁺ → U⁺ ⊗ U⁺` (twist `t`) with
`E ↦ E ⊗ 1 + 1 ⊗ E` exists iff `t = −1`. -/
theorem small_twisted_coproduct_exists_iff (t : GaussianInt) :
    (∃ f : uPlus →ₐ[GaussianInt] UPlusTensor t, f ε = tw evI t 1 0 + tw evI t 0 1) ↔ t = -1 := by
  constructor
  · rintro ⟨f, hf⟩
    have h := congrArg f (DualNumber.eps_mul_eps (R := GaussianInt))
    rw [map_mul, map_zero, hf, ← pow_two, tw_sq] at h
    have h' := congrArg (coeffAt evI t (1, 1)) h
    rw [map_smul, coeffAt_tw, ite_eq_left rfl, map_zero, smul_eq_mul, mul_one] at h'
    linear_combination h'
  · rintro rfl
    exact ⟨rU.comp iota, by rw [AlgHom.comp_apply, iota_eps, rU_E_one]⟩

end OddMath.Frontier.EQQuantum

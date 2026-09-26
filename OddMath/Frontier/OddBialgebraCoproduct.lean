import OddMath.Frontier.OddCategorification

/-!
# The `q`-bialgebra `U_q^+(sl_2)_A ≅ K₀(ONH)`

EKL arXiv:1111.1320v1, §6, pp. 46–47: induction and restriction "equip `K₀(ONH)` with the structure
of a `q`-bialgebra (for the notion of `q`-bialgebra see [EK, arXiv:1107.5610])". In Ellis–Khovanov
(§2.1, p. 5) a `q`-bialgebra is a bialgebra object in the category of `ℤ`-graded `k`-modules with
braiding `v ⊗ w ↦ q^{deg v deg w} w ⊗ v`: the multiplication of `H ⊗ H` is
`(x₁ ⊗ x₂)(y₁ ⊗ y₂) = q^{deg x₂ deg y₁} x₁y₁ ⊗ x₂y₂`, for any `q ∈ k`.

Here `k = A = ℤ[q,q⁻¹]`, `deg ϑ^{(a)} = a`, and the braiding parameter is `Q ∈ A`.

* `TwTensor Q`: the free `A`-module on `ϑ^{(a)} ⊗ ϑ^{(b)}` (`tw a b`) with EK's twisted product
  `(ϑ^{(a)} ⊗ ϑ^{(b)})(ϑ^{(c)} ⊗ ϑ^{(d)}) = Q^{bc} [a+c, a] [b+d, b] ϑ^{(a+c)} ⊗ ϑ^{(b+d)}`,
  an associative `A`-algebra; `tensorEquiv : TwTensor Q ≃ₗ K₀(ONH) ⊗_A K₀(ONH)`.
* For `Q = q^{-2}`: `Δ(ϑ^{(n)}) = ∑_{a+b=n} q^{-ab} ϑ^{(a)} ⊗ ϑ^{(b)}` is multiplicative
  (`coprodVal_mul`; `coprod`, an `A`-algebra map `U → U ⊗ U`), with counit `ε(ϑ^{(n)}) = δ_{n0}`
  (`counit`), counit laws (`counitLeft_coprod`, `counitRight_coprod`) and coassociativity
  (`coassoc`). It is the unique algebra map with `Δ(ϑ) = ϑ ⊗ 1 + 1 ⊗ ϑ` (`coprod_unique`), i.e.
  Lusztig's twisted coproduct `r` on `U^+` with `v = q⁻¹`. Transported along (6.3):
  `coprodK0`, `counitK0` on `K₀(ONH)`, with `U ⊗ U ≅ K₀(ONH) ⊗_A K₀(ONH)` (`tensorEquiv`).
* The braiding parameter is forced: a coproduct with `Δ(ϑ) = ϑ ⊗ 1 + 1 ⊗ ϑ` exists only if
  `[2] = q + q⁻¹` divides `1 + Q` (`coprod_dvd`); in particular the super-signed parameter
  `Q = -q^{-2}` admits none (`no_coprod_neg`). The super sign of `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`
  is invisible in `K₀`.

The coproduct is defined here on the basis `[E^{(a)}]`. Its categorical origin is treated in
`OddBialgebraRes` (restriction along `ONH_a ⊗ ONH_b ⊂ ONH_{a+b}`, `a, b ≥ 2`):
`[a+b]! (Res [E^{(a+b)}] - q^{-ab} [E^{(a)} ⊠ E^{(b)}]) = 0` in `K₀(ONH_a ⊗ ONH_b)`; the
identification `K₀(ONH_a ⊗ ONH_b) ≅ K₀(ONH_a) ⊗ K₀(ONH_b)` is not formalized.
-/

noncomputable section
open LaurentPolynomial Finset
open scoped TensorProduct

namespace OddMath.Frontier.OddBialgebra
open QuantumSl2Plus OddCategorification

local notation "A" => LaurentPolynomial ℤ

/-! ### The twisted tensor square -/

/-- `U ⊗_A U` with Ellis–Khovanov's twisted product, braiding parameter `Q`. -/
def TwTensor (_Q : A) : Type := ℕ × ℕ →₀ A

namespace TwTensor

variable {Q : A}

instance : AddCommGroup (TwTensor Q) := inferInstanceAs (AddCommGroup (ℕ × ℕ →₀ A))

instance : Module A (TwTensor Q) := inferInstanceAs (Module A (ℕ × ℕ →₀ A))

instance : NoZeroSMulDivisors A (TwTensor Q) :=
  inferInstanceAs (NoZeroSMulDivisors A (ℕ × ℕ →₀ A))

/-- `r ϑ^{(a)} ⊗ ϑ^{(b)}`. -/
def single (a b : ℕ) (r : A) : TwTensor Q := Finsupp.single (a, b) r

/-- `ϑ^{(a)} ⊗ ϑ^{(b)}`. -/
def tw (a b : ℕ) : TwTensor Q := single a b 1

variable (Q) in
/-- The basis `ϑ^{(a)} ⊗ ϑ^{(b)}`. -/
def basis : Basis (ℕ × ℕ) A (TwTensor Q) := Finsupp.basisSingleOne

theorem basis_apply (p : ℕ × ℕ) : basis Q p = tw p.1 p.2 := by
  exact congrFun (Finsupp.coe_basisSingleOne (R := A) (ι := ℕ × ℕ)) p

theorem single_eq_smul (a b : ℕ) (r : A) : (single a b r : TwTensor Q) = r • tw a b := by
  show Finsupp.single (a, b) r = r • Finsupp.single (a, b) (1 : A)
  rw [Finsupp.smul_single, smul_eq_mul, mul_one]

theorem induction_linear {p : TwTensor Q → Prop} (f : TwTensor Q) (h0 : p 0)
    (hadd : ∀ f g, p f → p g → p (f + g)) (hs : ∀ a b r, p (single a b r)) : p f :=
  Finsupp.induction_linear f h0 hadd fun x r => hs x.1 x.2 r

/-- The coefficient of `(ϑ^{(a)} ⊗ ϑ^{(b)})(ϑ^{(c)} ⊗ ϑ^{(d)})`. -/
def coeff (Q : A) (a b c d : ℕ) : A := Q ^ (b * c) * qBinom a c * qBinom b d

variable (Q) in
/-- The twisted product, as a bilinear map. -/
def mulL : TwTensor Q →ₗ[A] TwTensor Q →ₗ[A] TwTensor Q :=
  (basis Q).constr A fun p => (basis Q).constr A fun p' =>
    coeff Q p.1 p.2 p'.1 p'.2 • tw (p.1 + p'.1) (p.2 + p'.2)

instance : Mul (TwTensor Q) := ⟨fun x y => mulL Q x y⟩

instance : One (TwTensor Q) := ⟨tw 0 0⟩

theorem mul_def (x y : TwTensor Q) : x * y = mulL Q x y := rfl

theorem one_def : (1 : TwTensor Q) = tw 0 0 := rfl

theorem qBinom_one (a : ℕ) : qBinom a 1 = qInt (a + 1) := by
  have h := qBinom_mul_qFact a 1
  rw [qFact_succ a, show qFact 1 = 1 by simp [qFact, qInt], mul_one] at h
  exact mul_right_cancel₀ (qFact_ne_zero a) (h.trans (mul_comm _ _))

theorem tw_mul_tw (a b c d : ℕ) :
    (tw a b : TwTensor Q) * tw c d = coeff Q a b c d • tw (a + c) (b + d) := by
  rw [mul_def, ← basis_apply (a, b), ← basis_apply (c, d), mulL, Basis.constr_basis,
    Basis.constr_basis]

theorem single_mul_single (a b c d : ℕ) (r s : A) :
    (single a b r : TwTensor Q) * single c d s =
      single (a + c) (b + d) (coeff Q a b c d * r * s) := by
  rw [single_eq_smul, single_eq_smul, single_eq_smul, mul_def, map_smul, map_smul,
    LinearMap.smul_apply, ← mul_def, tw_mul_tw, smul_smul, smul_smul]
  ring_nf

theorem coeff_assoc (a b c d e f : ℕ) :
    coeff Q a b c d * coeff Q (a + c) (b + d) e f =
      coeff Q c d e f * coeff Q a b (c + e) (d + f) := by
  have h1 := qBinom_assoc a c e
  have h2 := qBinom_assoc b d f
  have hQ : Q ^ (b * c) * Q ^ ((b + d) * e) = Q ^ (d * e) * Q ^ (b * (c + e)) := by
    rw [← pow_add, ← pow_add]
    congr 1
    ring
  simp only [coeff]
  linear_combination (Q ^ (b * c) * Q ^ ((b + d) * e) * qBinom b d * qBinom (b + d) f) * h1 +
    (Q ^ (d * e) * qBinom c e * qBinom a (c + e) * Q ^ (b * (c + e))) * h2 +
    (qBinom a c * qBinom (a + c) e * qBinom b d * qBinom (b + d) f) * hQ

private theorem mul_assoc' (x y z : TwTensor Q) : x * y * z = x * (y * z) := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hx, hx']
  | hs a b r =>
    induction y using induction_linear with
    | h0 => simp [mul_def]
    | hadd y y' hy hy' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hy, hy']
    | hs c d s =>
      induction z using induction_linear with
      | h0 => simp [mul_def]
      | hadd z z' hz hz' => simp only [mul_def, map_add] at *; rw [hz, hz']
      | hs e f t =>
        simp only [single_mul_single, add_assoc]
        congr 1
        linear_combination r * s * t * coeff_assoc a b c d e f

private theorem one_mul' (x : TwTensor Q) : 1 * x = x := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add] at *; rw [hx, hx']
  | hs a b r =>
    rw [one_def, tw, single_mul_single, zero_add, zero_add]
    simp [coeff]

private theorem mul_one' (x : TwTensor Q) : x * 1 = x := by
  induction x using induction_linear with
  | h0 => simp [mul_def]
  | hadd x x' hx hx' => simp only [mul_def, map_add, LinearMap.add_apply] at *; rw [hx, hx']
  | hs a b r =>
    rw [one_def, tw, single_mul_single, add_zero, add_zero]
    simp [coeff]

instance : Ring (TwTensor Q) :=
  { (inferInstance : AddCommGroup (TwTensor Q)) with
    mul := (· * ·)
    one := 1
    left_distrib := fun x y z => map_add (mulL Q x) y z
    right_distrib := fun x y z => by simp only [mul_def, map_add, LinearMap.add_apply]
    zero_mul := fun x => by simp only [mul_def, map_zero, LinearMap.zero_apply]
    mul_zero := fun x => map_zero (mulL Q x)
    mul_assoc := mul_assoc'
    one_mul := one_mul'
    mul_one := mul_one' }

instance : Algebra A (TwTensor Q) :=
  Algebra.ofModule (fun r x y => by simp only [mul_def, map_smul, LinearMap.smul_apply])
    (fun r x y => map_smul (mulL Q x) r y)

end TwTensor

namespace TwTensor

variable {Q : A}

theorem single_zero (a b : ℕ) : (single a b 0 : TwTensor Q) = 0 := Finsupp.single_zero _

theorem tw_mul_tw_one_zero (a b : ℕ) :
    (tw a b : TwTensor Q) * tw 1 0 = (Q ^ b * qInt (a + 1)) • tw (a + 1) b := by
  rw [tw_mul_tw, coeff, qBinom_zero_right, mul_one, mul_one, qBinom_one, add_zero]

theorem tw_mul_tw_zero_one (a b : ℕ) :
    (tw a b : TwTensor Q) * tw 0 1 = qInt (b + 1) • tw a (b + 1) := by
  rw [tw_mul_tw, coeff, qBinom_zero_right, mul_zero, pow_zero, one_mul, one_mul, qBinom_one,
    add_zero]

variable (Q) in
/-- The coefficient of `ϑ^{(a)} ⊗ ϑ^{(b)}`. -/
def coeffAt (p : ℕ × ℕ) : TwTensor Q →ₗ[A] A := Finsupp.lapply p

theorem coeffAt_single (p : ℕ × ℕ) (a b : ℕ) (r : A) :
    coeffAt Q p (single a b r) = if (a, b) = p then r else 0 := by
  show Finsupp.single (a, b) r p = _
  rw [Finsupp.single_apply]

end TwTensor

open TwTensor

/-! ### The coproduct -/

/-- `Δ(ϑ^{(n)}) = ∑_{a+b=n} q^{-ab} ϑ^{(a)} ⊗ ϑ^{(b)}`, braiding parameter `q^{-2}`. -/
def coprodVal (n : ℕ) : TwTensor (T (-2)) :=
  ∑ p ∈ antidiagonal n, (T (-((p.1 * p.2 : ℕ) : ℤ)) : A) • tw p.1 p.2

theorem coprodVal_zero : coprodVal 0 = 1 := by
  simp [coprodVal, TwTensor.one_def]

theorem coprodVal_one : coprodVal 1 = tw 1 0 + tw 0 1 := by
  rw [coprodVal, Nat.sum_antidiagonal_succ', antidiagonal_zero, sum_singleton]
  simp

theorem coprodVal_mul_one (n : ℕ) :
    coprodVal n * coprodVal 1 = qInt (n + 1) • coprodVal (n + 1) := by
  have hR : qInt (n + 1) • coprodVal (n + 1) =
      (∑ q ∈ antidiagonal (n + 1), (T (-(q.2 : ℤ)) * qInt q.1 *
        T (-((q.1 * q.2 : ℕ) : ℤ)) : A) • (tw q.1 q.2 : TwTensor (T (-2)))) +
      ∑ q ∈ antidiagonal (n + 1), (T (q.1 : ℤ) * qInt q.2 *
        T (-((q.1 * q.2 : ℕ) : ℤ)) : A) • (tw q.1 q.2 : TwTensor (T (-2))) := by
    rw [coprodVal, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun q hq => ?_
    rw [mem_antidiagonal] at hq
    rw [smul_smul, ← add_smul, ← hq, add_comm q.1 q.2, qInt_add]
    congr 1
    ring
  rw [hR, Nat.sum_antidiagonal_succ, Nat.sum_antidiagonal_succ', coprodVal_one, mul_add, coprodVal,
    sum_mul, sum_mul, add_comm (∑ i ∈ antidiagonal n, _ * tw 1 0)]
  simp only [qInt_zero, mul_zero, zero_mul, zero_smul, zero_add, smul_mul_assoc,
    tw_mul_tw_one_zero, tw_mul_tw_zero_one, smul_smul]
  rw [add_comm]
  congr 1 <;> refine sum_congr rfl fun p _ => ?_ <;> congr 1
  · rw [T_pow, ← mul_assoc, ← T_add, mul_right_comm, ← T_add]
    congr 2
    push_cast
    ring
  · rw [mul_right_comm, ← T_add]
    congr 2
    push_cast
    ring

theorem coprodVal_one_pow (n : ℕ) : coprodVal 1 ^ n = qFact n • coprodVal n := by
  induction n with
  | zero => rw [pow_zero, coprodVal_zero, qFact, range_zero, prod_empty, one_smul]
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, coprodVal_mul_one, smul_smul, qFact_succ]

/-- `Δ(ϑ^{(a)}) Δ(ϑ^{(b)}) = [a+b, a] Δ(ϑ^{(a+b)})` in the twisted tensor square. -/
theorem coprodVal_mul (a b : ℕ) :
    coprodVal a * coprodVal b = qBinom a b • coprodVal (a + b) := by
  refine smul_right_injective (TwTensor (T (-2))) (mul_ne_zero (qFact_ne_zero a)
    (qFact_ne_zero b)) ?_
  simp only
  rw [← smul_mul_smul_comm, ← coprodVal_one_pow, ← coprodVal_one_pow, ← pow_add,
    coprodVal_one_pow, smul_smul, ← qBinom_mul_qFact a b]
  congr 1
  ring

/-- **The coproduct** `Δ : U_q^+(sl_2)_A → U ⊗ U` (twisted product, parameter `q^{-2}`),
`Δ(ϑ^{(n)}) = ∑_{a+b=n} q^{-ab} ϑ^{(a)} ⊗ ϑ^{(b)}`, an `A`-algebra map. -/
def coprod : DivPowAlg →ₐ[A] TwTensor (T (-2)) :=
  DivPowAlg.lift coprodVal coprodVal_zero coprodVal_mul

theorem coprod_θ (n : ℕ) : coprod (DivPowAlg.θ n) = coprodVal n := DivPowAlg.lift_θ _ _ _ _

/-- The counit `ε(ϑ^{(n)}) = δ_{n0}`. -/
def counit : DivPowAlg →ₐ[A] A :=
  DivPowAlg.lift (fun n => if n = 0 then 1 else 0) (by simp) fun a b => by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · simp
      · simp [hb.ne']
    · simp [ha.ne']

theorem counit_θ (n : ℕ) : counit (DivPowAlg.θ n) = if n = 0 then 1 else 0 :=
  DivPowAlg.lift_θ _ _ _ _

theorem tw_eq_basis {Q : A} (a b : ℕ) : (tw a b : TwTensor Q) = basis Q (a, b) :=
  (basis_apply (a, b)).symm

theorem constr_tw {Q : A} {M : Type*} [AddCommGroup M] [Module A M] (f : ℕ × ℕ → M) (a b : ℕ) :
    (basis Q).constr A f (tw a b) = f (a, b) := by
  rw [tw_eq_basis, Basis.constr_basis]

/-! ### Counit laws -/

/-- `ε ⊗ id : U ⊗ U → U`, `ϑ^{(a)} ⊗ ϑ^{(b)} ↦ ε(ϑ^{(a)}) ϑ^{(b)}`. -/
def counitLeft : TwTensor (T (-2)) →ₗ[A] DivPowAlg :=
  (basis _).constr A fun p => counit (DivPowAlg.θ p.1) • DivPowAlg.θ p.2

/-- `id ⊗ ε : U ⊗ U → U`, `ϑ^{(a)} ⊗ ϑ^{(b)} ↦ ε(ϑ^{(b)}) ϑ^{(a)}`. -/
def counitRight : TwTensor (T (-2)) →ₗ[A] DivPowAlg :=
  (basis _).constr A fun p => counit (DivPowAlg.θ p.2) • DivPowAlg.θ p.1

/-- `(ε ⊗ id) ∘ Δ = id`. -/
theorem counitLeft_coprod (x : DivPowAlg) : counitLeft (coprod x) = x := by
  have h : counitLeft ∘ₗ coprod.toLinearMap = LinearMap.id :=
    DivPowAlg.basis.ext fun n => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DivPowAlg.basis_apply, coprod_θ,
        coprodVal, map_sum, LinearMap.id_apply]
      rw [sum_eq_single (0, n)]
      · rw [map_smul, counitLeft, constr_tw, counit_θ, if_pos rfl, one_smul]
        simp
      · rintro ⟨a, b⟩ _ hab
        rw [map_smul, counitLeft, constr_tw, counit_θ, if_neg, zero_smul, smul_zero]
        rintro rfl
        simp_all
      · intro h
        exact absurd (mem_antidiagonal.2 (zero_add n)) h
  exact DFunLike.congr_fun h x

/-- `(id ⊗ ε) ∘ Δ = id`. -/
theorem counitRight_coprod (x : DivPowAlg) : counitRight (coprod x) = x := by
  have h : counitRight ∘ₗ coprod.toLinearMap = LinearMap.id :=
    DivPowAlg.basis.ext fun n => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DivPowAlg.basis_apply, coprod_θ,
        coprodVal, map_sum, LinearMap.id_apply]
      rw [sum_eq_single (n, 0)]
      · rw [map_smul, counitRight, constr_tw, counit_θ, if_pos rfl, one_smul]
        simp
      · rintro ⟨a, b⟩ hab hne
        rw [map_smul, counitRight, constr_tw, counit_θ, if_neg, zero_smul, smul_zero]
        rintro rfl
        simp only [mem_antidiagonal, add_zero] at hab
        exact hne (Prod.ext hab rfl)
      · intro h
        exact absurd (mem_antidiagonal.2 (add_zero n)) h
  exact DFunLike.congr_fun h x

/-! ### Coassociativity -/

/-- The free `A`-module on `ϑ^{(a)} ⊗ ϑ^{(b)} ⊗ ϑ^{(c)}`. -/
abbrev Tw3 : Type := ℕ × ℕ × ℕ →₀ A

/-- `Δ ⊗ id : U ⊗ U → U ⊗ U ⊗ U`. -/
def coprodLeft : TwTensor (T (-2)) →ₗ[A] Tw3 :=
  (basis _).constr A fun p =>
    Finsupp.lmapDomain A A (fun q : ℕ × ℕ => (q.1, q.2, p.2)) (coprodVal p.1)

/-- `id ⊗ Δ : U ⊗ U → U ⊗ U ⊗ U`. -/
def coprodRight : TwTensor (T (-2)) →ₗ[A] Tw3 :=
  (basis _).constr A fun p =>
    Finsupp.lmapDomain A A (fun q : ℕ × ℕ => (p.1, q.1, q.2)) (coprodVal p.2)

theorem lmapDomain_tw (f : ℕ × ℕ → ℕ × ℕ × ℕ) (a b : ℕ) :
    Finsupp.lmapDomain A A f (tw a b : TwTensor (T (-2))) = Finsupp.single (f (a, b)) 1 :=
  Finsupp.mapDomain_single

/-- **Coassociativity** `(Δ ⊗ id) ∘ Δ = (id ⊗ Δ) ∘ Δ`. -/
theorem coassoc (x : DivPowAlg) : coprodLeft (coprod x) = coprodRight (coprod x) := by
  have h : coprodLeft ∘ₗ coprod.toLinearMap = coprodRight ∘ₗ coprod.toLinearMap :=
    DivPowAlg.basis.ext fun n => by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, DivPowAlg.basis_apply,
        coprod_θ, coprodVal, map_sum, map_smul, coprodLeft, coprodRight, constr_tw,
        lmapDomain_tw, smul_sum, smul_smul, sum_sigma']
      refine sum_nbij' (fun x => ⟨(x.2.1, x.2.2 + x.1.2), (x.2.2, x.1.2)⟩)
        (fun x => ⟨(x.1.1 + x.2.1, x.2.2), (x.1.1, x.2.1)⟩) ?_ ?_ ?_ ?_ ?_
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, mem_antidiagonal, and_true] at hx ⊢
        omega
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, mem_antidiagonal, and_true] at hx ⊢
        omega
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, mem_antidiagonal] at hx
        obtain ⟨h1, h2⟩ := hx
        subst h2
        simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true]
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, mem_antidiagonal] at hx
        obtain ⟨h1, h2⟩ := hx
        subst h2
        simp only [Sigma.mk.injEq, Prod.mk.injEq, heq_eq_eq, and_true]
      · rintro ⟨⟨a, b⟩, ⟨i, j⟩⟩ hx
        simp only [mem_sigma, mem_antidiagonal] at hx
        obtain ⟨rfl, rfl⟩ := hx
        simp only
        rw [← T_add, ← T_add]
        congr 2
        push_cast
        ring
  exact DFunLike.congr_fun h x

/-! ### Uniqueness, and the braiding parameter -/

theorem θ_one_pow (n : ℕ) : DivPowAlg.θ 1 ^ n = qFact n • DivPowAlg.θ n := by
  induction n with
  | zero => rw [pow_zero, DivPowAlg.one_def, qFact, range_zero, prod_empty, one_smul]
  | succ n ih =>
    rw [pow_succ, ih, smul_mul_assoc, DivPowAlg.θ_mul_θ, smul_smul, qFact_succ,
      TwTensor.qBinom_one]

/-- `Δ` is the unique `A`-algebra map with `Δ(ϑ) = ϑ ⊗ 1 + 1 ⊗ ϑ`: Lusztig's `r` on
`U_q^+(sl_2)_A` (with `v = q⁻¹`). -/
theorem coprod_unique (f : DivPowAlg →ₐ[A] TwTensor (T (-2)))
    (h : f (DivPowAlg.θ 1) = tw 1 0 + tw 0 1) : f = coprod :=
  DivPowAlg.algHom_ext fun n => smul_right_injective (TwTensor (T (-2))) (qFact_ne_zero n) <| by
    simp only
    rw [← map_smul, ← map_smul, ← θ_one_pow, map_pow, map_pow, h, coprod_θ, coprodVal_one]

theorem qFact_two : qFact 2 = qInt 2 := by
  simp [qFact, prod_range_succ, qInt]

/-- For any braiding parameter `Q`, a coproduct on `U_q^+(sl_2)_A` with `Δ(ϑ) = ϑ ⊗ 1 + 1 ⊗ ϑ`
forces `[2] ∣ 1 + Q` (compare the coefficient of `ϑ ⊗ ϑ` in `Δ(ϑ)² = [2] Δ(ϑ^{(2)})`). -/
theorem coprod_dvd {Q : A} (f : DivPowAlg →ₐ[A] TwTensor Q)
    (h : f (DivPowAlg.θ 1) = tw 1 0 + tw 0 1) : qInt 2 ∣ 1 + Q := by
  have h2 : f (DivPowAlg.θ 1) ^ 2 = qInt 2 • f (DivPowAlg.θ 2) := by
    rw [← map_pow, θ_one_pow, map_smul, qFact_two]
  rw [h] at h2
  have h3 := congrArg (coeffAt Q (1, 1)) h2
  rw [map_smul, smul_eq_mul] at h3
  refine ⟨_, Eq.trans ?_ h3⟩
  simp only [pow_two, add_mul, mul_add, tw_mul_tw, map_add, map_smul, smul_eq_mul, coeff]
  simp [tw, coeffAt_single, add_comm]

/-- `q + q⁻¹ ∤ 1 - q^{-2}` in `ℤ[q,q⁻¹]` (evaluate at `q = 2` in `𝔽₅`). -/
theorem qInt_two_not_dvd : ¬ qInt 2 ∣ 1 + -(T (-2) : A) := by
  let u : (ZMod 5)ˣ := ⟨2, 3, by decide, by decide⟩
  let φ : A →+* ZMod 5 := LaurentPolynomial.eval₂ (Int.castRingHom (ZMod 5)) u
  rintro ⟨c, hc⟩
  have h := congrArg φ hc
  have e1 : φ (qInt 2) = 0 := by
    simp only [φ, qInt, sum_range_succ, range_zero, sum_empty, map_add, map_zero, zero_add,
      eval₂_T]
    norm_num
    decide
  have e2 : φ (1 + -T (-2)) = 2 := by
    simp only [φ, map_add, map_neg, map_one, eval₂_T]
    decide
  rw [map_mul, e1, zero_mul, e2] at h
  exact absurd h (by decide)

/-- **No super sign in `K₀`.** With the super-signed braiding parameter `-q^{-2}` there is no
coproduct on `U_q^+(sl_2)_A` with `Δ(ϑ) = ϑ ⊗ 1 + 1 ⊗ ϑ`. -/
theorem no_coprod_neg :
    ¬ ∃ f : DivPowAlg →ₐ[A] TwTensor (-(T (-2) : A)), f (DivPowAlg.θ 1) = tw 1 0 + tw 0 1 :=
  fun ⟨f, h⟩ => qInt_two_not_dvd (coprod_dvd f h)

/-! ### Transport to `K₀(ONH)` -/

/-- `U ⊗ U ≃ K₀(ONH) ⊗_A K₀(ONH)`, `ϑ^{(a)} ⊗ ϑ^{(b)} ↦ [E^{(a)}] ⊗ [E^{(b)}]`. -/
def tensorEquiv (Q : A) : TwTensor Q ≃ₗ[A] K0ONH ⊗[A] K0ONH :=
  (basisK0.tensorProduct basisK0).repr.symm

theorem tensorEquiv_tw (Q : A) (a b : ℕ) :
    tensorEquiv Q (tw a b) =
      (DFinsupp.single a (Eclass a) : K0ONH) ⊗ₜ[A] (DFinsupp.single b (Eclass b) : K0ONH) := by
  rw [tensorEquiv, ← basisK0_apply, ← basisK0_apply, ← Basis.tensorProduct_apply]
  exact (basisK0.tensorProduct basisK0).repr_symm_single (a, b) 1 |>.trans (one_smul _ _)

/-- The coproduct of `K₀(ONH)` (on the basis `[E^{(a)}]`, through (6.3)). -/
def coprodK0 : K0ONH →ₐ[A] TwTensor (T (-2)) := coprod.comp eq_6_3.symm.toAlgHom

/-- The counit of `K₀(ONH)`. -/
def counitK0 : K0ONH →ₐ[A] A := counit.comp eq_6_3.symm.toAlgHom

theorem coprodK0_E (n : ℕ) :
    tensorEquiv _ (coprodK0 (DFinsupp.single n (Eclass n))) =
      ∑ p ∈ antidiagonal n, (T (-((p.1 * p.2 : ℕ) : ℤ)) : A) •
        (DFinsupp.single p.1 (Eclass p.1) : K0ONH) ⊗ₜ[A]
          (DFinsupp.single p.2 (Eclass p.2) : K0ONH) := by
  rw [coprodK0, AlgHom.comp_apply, ← eq_6_3_θ, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    AlgEquiv.symm_apply_apply, coprod_θ, coprodVal, ← LinearEquiv.coe_toLinearMap, map_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [LinearMap.map_smul, LinearEquiv.coe_toLinearMap, tensorEquiv_tw]

theorem counitK0_E (n : ℕ) :
    counitK0 (DFinsupp.single n (Eclass n)) = if n = 0 then 1 else 0 := by
  rw [counitK0, AlgHom.comp_apply, ← eq_6_3_θ, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
    AlgEquiv.symm_apply_apply, counit_θ]

end OddMath.Frontier.OddBialgebra

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic

/-!
# Localized polynomial–Clifford coefficients on infinitely many strands

Kang–Kashiwara–Tsuchioka, *Quiver Hecke superalgebras*, arXiv:1107.1039v2, §3.4: the
coefficient superalgebra `MK_n` of the realization (Theorem 3.8), with ordinary polynomial
variables `y_p` localized at the differences and sums `y_a ∓ y_b`, and Clifford generators
`c_p` with `c_p² = 1`, `c_p c_q = -c_q c_p` and `c_p y_p = -y_p c_p`.

The positions are indexed by `ℕ`, so that the same coefficient module serves words of every
length. We use the total quotient ring of `k[y_p : p ∈ ℕ]`, which contains KKT's localization;
`y_a ∓ y_b` are non-zero-divisors over any commutative ring `k`.

Elements of `Coeff k = K ⊗ Cl` are written `f ⊗ u` for the product `f · u`, polynomial factor
first. On these, multiplication on the left by a scalar `g` is `scalar g`, and multiplication on
the left by `c_p` is `cliff p : f ⊗ u ↦ r_p(f) ⊗ c_p u`, where `r_p` changes the sign of `y_p`.
Permutations of the strands act on both factors (`perm`).

No invertibility of two is used here.
-/

noncomputable section
open scoped TensorProduct nonZeroDivisors
namespace OddMath.QuiverHecke.Realization

variable (k : Type*) [CommRing k]

/-! ## Localized polynomial scalars -/

/-- Polynomials in the variables `y_p`, `p ∈ ℕ`. -/
abbrev P := MvPolynomial ℕ k

/-- The total quotient ring of `P`. -/
abbrev K := FractionRing (P k)

variable {k}

/-- The localized variable `y_p`. -/
def y (p : ℕ) : K k := algebraMap (P k) (K k) (MvPolynomial.X p)

/-- A polynomial change of variables carrying `y_a` to `y_a + c y_b`. -/
def transvection (a b : ℕ) (hab : a ≠ b) (c : k) : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun q => if q = a then
      MvPolynomial.X a + MvPolynomial.C c * MvPolynomial.X b else MvPolynomial.X q)
    (MvPolynomial.aeval fun q => if q = a then
      MvPolynomial.X a - MvPolynomial.C c * MvPolynomial.X b else MvPolynomial.X q)
    (by ext q; by_cases h : q = a <;> simp [h, Ne.symm hab])
    (by ext q; by_cases h : q = a <;> simp [h, Ne.symm hab])

theorem X_add_C_mul_X_mem (a b : ℕ) (hab : a ≠ b) (c : k) :
    MvPolynomial.X a + MvPolynomial.C c * MvPolynomial.X b ∈ (P k)⁰ := by
  have h := MulEquivClass.map_nonZeroDivisors (transvection a b hab c)
  rw [← h]
  exact ⟨MvPolynomial.X a, MvPolynomial.isRegular_X.mem_nonZeroDivisors,
    by simp [transvection]⟩

/-- `y_a - y_b` is a unit for `a ≠ b`. -/
theorem isUnit_y_sub {a b : ℕ} (hab : a ≠ b) : IsUnit (y (k := k) a - y b) := by
  have h := X_add_C_mul_X_mem (k := k) a b hab (-1)
  simp only [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg] at h
  simpa only [y, map_sub] using IsLocalization.map_units (K k)
    (⟨MvPolynomial.X a - MvPolynomial.X b, h⟩ : (P k)⁰)

/-- `y_a + y_b` is a unit for `a ≠ b`, in every characteristic. -/
theorem isUnit_y_add {a b : ℕ} (hab : a ≠ b) : IsUnit (y (k := k) a + y b) := by
  have h := X_add_C_mul_X_mem (k := k) a b hab 1
  simp only [map_one, one_mul] at h
  simpa only [y, map_add] using IsLocalization.map_units (K k)
    (⟨MvPolynomial.X a + MvPolynomial.X b, h⟩ : (P k)⁰)

theorem algebraMap_injective : Function.Injective (algebraMap (P k) (K k)) :=
  IsFractionRing.injective (P k) (K k)

/-- Permutation of the variables. -/
def permK (σ : Equiv.Perm ℕ) : K k ≃ₐ[k] K k :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv k σ)

@[simp] theorem permK_y (σ : Equiv.Perm ℕ) (p : ℕ) : permK (k := k) σ (y p) = y (σ p) := by
  simp [permK, y, MvPolynomial.renameEquiv]

/-- Two `k`-algebra maps out of `K` agreeing on all `y_p` are equal. -/
theorem algHom_ext_y {f g : K k →ₐ[k] K k} (h : ∀ p, f (y p) = g (y p)) : f = g :=
  IsLocalization.algHom_ext (P k)⁰ (MvPolynomial.algHom_ext fun p => h p)

theorem permK_mul (σ τ : Equiv.Perm ℕ) (f : K k) :
    permK (σ * τ) f = permK σ (permK τ f) := by
  have : (permK (k := k) (σ * τ)).toAlgHom = (permK σ).toAlgHom.comp (permK τ).toAlgHom :=
    algHom_ext_y fun p => by simp
  exact DFunLike.congr_fun this f

@[simp] theorem permK_one (f : K k) : permK 1 f = f := by
  have : (permK (k := k) 1).toAlgHom = AlgHom.id k (K k) := algHom_ext_y fun p => by simp
  exact DFunLike.congr_fun this f

/-- Change of sign of one variable. -/
def reflection (p : ℕ) : P k ≃ₐ[k] P k :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun q => if q = p then -MvPolynomial.X q else MvPolynomial.X q)
    (MvPolynomial.aeval fun q => if q = p then -MvPolynomial.X q else MvPolynomial.X q)
    (by ext q; by_cases h : q = p <;> simp [h])
    (by ext q; by_cases h : q = p <;> simp [h])

/-- The reflection `r_p : y_p ↦ -y_p` on `K`. -/
def reflect (p : ℕ) : K k ≃ₐ[k] K k :=
  IsFractionRing.algEquivOfAlgEquiv (reflection p)

@[simp] theorem reflect_y (p q : ℕ) :
    reflect (k := k) p (y q) = if q = p then -y q else y q := by
  by_cases h : q = p <;> simp [reflect, reflection, y, h]

@[simp] theorem reflect_y_self (p : ℕ) : reflect (k := k) p (y p) = -y p := by simp

theorem reflect_y_of_ne {p q : ℕ} (h : q ≠ p) : reflect (k := k) p (y q) = y q := by simp [h]

@[simp] theorem reflect_reflect (p : ℕ) (f : K k) : reflect p (reflect p f) = f := by
  have : (reflect (k := k) p).toAlgHom.comp (reflect p).toAlgHom = AlgHom.id k (K k) :=
    algHom_ext_y fun q => by by_cases h : q = p <;> simp [h]
  exact DFunLike.congr_fun this f

theorem reflect_comm (p q : ℕ) (f : K k) : reflect p (reflect q f) = reflect q (reflect p f) := by
  have : (reflect (k := k) p).toAlgHom.comp (reflect q).toAlgHom =
      (reflect q).toAlgHom.comp (reflect p).toAlgHom :=
    algHom_ext_y fun r => by by_cases hp : r = p <;> by_cases hq : r = q <;> simp_all
  exact DFunLike.congr_fun this f

theorem permK_reflect (σ : Equiv.Perm ℕ) (p : ℕ) (f : K k) :
    permK σ (reflect p f) = reflect (σ p) (permK σ f) := by
  have : (permK (k := k) σ).toAlgHom.comp (reflect p).toAlgHom =
      (reflect (σ p)).toAlgHom.comp (permK σ).toAlgHom :=
    algHom_ext_y fun q => by by_cases h : q = p <;> simp [h]
  exact DFunLike.congr_fun this f

/-- A scalar not involving `y_p` (in the sense that `r_p` fixes it) is fixed by permutations
fixing `p`; we record the basic instance for scalars built from `y_q`, `q ≠ p`. -/
theorem reflect_y_sub_of_ne {p a b : ℕ} (ha : a ≠ p) (hb : b ≠ p) :
    reflect (k := k) p (y a - y b) = y a - y b := by simp [ha, hb]

/-! ## The Clifford algebra -/

variable (k)

/-- The standard dot product on `ℕ →₀ k`. -/
def dot : LinearMap.BilinForm k (ℕ →₀ k) :=
  Finsupp.lsum k fun p => (LinearMap.mul k k).compl₂ (Finsupp.lapply p)

@[simp] theorem dot_single (p q : ℕ) (a b : k) :
    dot k (Finsupp.single p a) (Finsupp.single q b) = if p = q then a * b else 0 := by
  by_cases h : p = q
  · subst h; simp [dot]
  · simp [dot, h]

/-- The quadratic form `∑ v_p²`. -/
def form : QuadraticForm k (ℕ →₀ k) := (dot k).toQuadraticMap

/-- The Clifford algebra with orthonormal generators `c_p`. -/
abbrev Cl := CliffordAlgebra (form k)

variable {k}

/-- The Clifford generator `c_p`. -/
def c (p : ℕ) : Cl k := CliffordAlgebra.ι (form k) (Finsupp.single p 1)

@[simp] theorem c_mul_self (p : ℕ) : c (k := k) p * c p = 1 := by
  rw [c, CliffordAlgebra.ι_sq_scalar]
  simp only [form, LinearMap.BilinMap.toQuadraticMap_apply, dot_single, ite_true, mul_one]
  exact map_one _

theorem c_anticomm {p q : ℕ} (h : p ≠ q) : c (k := k) p * c q = -(c q * c p) := by
  rw [eq_neg_iff_add_eq_zero, c, c, CliffordAlgebra.ι_mul_ι_add_swap]
  simp only [form, LinearMap.BilinMap.polar_toQuadraticMap, dot_single, h, Ne.symm h, ite_false,
    add_zero]
  exact map_zero _

theorem dot_domLCongr (σ : Equiv.Perm ℕ) (u v : ℕ →₀ k) :
    dot k ((Finsupp.domLCongr σ : (ℕ →₀ k) ≃ₗ[k] (ℕ →₀ k)) u)
      ((Finsupp.domLCongr σ : (ℕ →₀ k) ≃ₗ[k] (ℕ →₀ k)) v) = dot k u v := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u u' hu hu' => simp only [map_add, LinearMap.add_apply, hu, hu']
  | single p a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v v' hv hv' => rw [map_add, map_add, map_add, hv, hv']
    | single q b => simp [σ.injective.eq_iff]

/-- A permutation of the coordinates is an isometry. -/
def permForm (σ : Equiv.Perm ℕ) : (form k).IsometryEquiv (form k) where
  toLinearEquiv := Finsupp.domLCongr σ
  map_app' v := by
    change dot k (Finsupp.domLCongr σ v) (Finsupp.domLCongr σ v) = dot k v v
    exact dot_domLCongr σ v v

/-- The induced permutation of the Clifford generators. -/
def permCl (σ : Equiv.Perm ℕ) : Cl k ≃ₐ[k] Cl k :=
  CliffordAlgebra.equivOfIsometry (permForm σ)

@[simp] theorem permCl_c (σ : Equiv.Perm ℕ) (p : ℕ) : permCl (k := k) σ (c p) = c (σ p) := by
  simp only [permCl, c, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  congr 1
  exact Finsupp.domLCongr_single σ p 1

theorem permCl_ι (σ : Equiv.Perm ℕ) (v : ℕ →₀ k) :
    permCl (k := k) σ (CliffordAlgebra.ι (form k) v) =
      CliffordAlgebra.ι (form k) ((Finsupp.domLCongr σ : (ℕ →₀ k) ≃ₗ[k] (ℕ →₀ k)) v) := by
  simp only [permCl, CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_apply_ι]
  rfl

theorem permCl_mul (σ τ : Equiv.Perm ℕ) (u : Cl k) :
    permCl (σ * τ) u = permCl σ (permCl τ u) := by
  have : (permCl (k := k) (σ * τ)).toAlgHom = (permCl σ).toAlgHom.comp (permCl τ).toAlgHom := by
    refine CliffordAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    change permCl (σ * τ) (CliffordAlgebra.ι (form k) v) =
      permCl σ (permCl τ (CliffordAlgebra.ι (form k) v))
    rw [permCl_ι, permCl_ι, permCl_ι]
    congr 1
    ext q
    simp [Finsupp.domLCongr_apply, Equiv.Perm.mul_def]
  exact DFunLike.congr_fun this u

@[simp] theorem permCl_one (u : Cl k) : permCl 1 u = u := by
  have : (permCl (k := k) 1).toAlgHom = AlgHom.id k (Cl k) := by
    refine CliffordAlgebra.hom_ext (LinearMap.ext fun v => ?_)
    change permCl 1 (CliffordAlgebra.ι (form k) v) = CliffordAlgebra.ι (form k) v
    rw [permCl_ι]
    congr 1
    ext q
    simp [Finsupp.domLCongr_apply]; rfl
  exact DFunLike.congr_fun this u

/-! ## The coefficient module and its basic operators -/

/-- `mul_neg` for linear endomorphisms. Negation of linear maps is elaborated through
`LinearMap.instNeg`, which `rw` and `simp` do not match with the negation of the ring
`Module.End`; this restatement uses the former. -/
theorem endMul_neg {X : Type*} [AddCommGroup X] [Module k X] (a b : Module.End k X) :
    a * -b = -(a * b) := mul_neg a b

/-- `neg_zero` for linear endomorphisms; see `endMul_neg`. -/
@[simp] theorem endNeg_zero {X : Type*} [AddCommGroup X] [Module k X] :
    -(0 : Module.End k X) = 0 := neg_zero

/-- `neg_mul` for linear endomorphisms; see `endMul_neg`. -/
theorem endNeg_mul {X : Type*} [AddCommGroup X] [Module k X] (a b : Module.End k X) :
    -a * b = -(a * b) := neg_mul a b

variable (k)

/-- The coefficient module `K ⊗ Cl`; `f ⊗ u` stands for `f · u`. -/
abbrev Coeff := K k ⊗[k] Cl k

variable {k}

/-- Left multiplication by a scalar `g ∈ K`. -/
def scalar (g : K k) : Module.End k (Coeff k) :=
  TensorProduct.map (Algebra.lmul k (K k) g) LinearMap.id

@[simp] theorem scalar_tmul (g f : K k) (u : Cl k) :
    scalar g (f ⊗ₜ[k] u) = (g * f) ⊗ₜ[k] u := by simp [scalar]

/-- Left multiplication by `c_p`: `c_p · f u = r_p(f) · c_p u`. -/
def cliff (p : ℕ) : Module.End k (Coeff k) :=
  TensorProduct.map (reflect p).toLinearMap (Algebra.lmul k (Cl k) (c p))

@[simp] theorem cliff_tmul (p : ℕ) (f : K k) (u : Cl k) :
    cliff p (f ⊗ₜ[k] u) = reflect p f ⊗ₜ[k] (c p * u) := by simp [cliff]

/-- Simultaneous permutation of the variables and Clifford generators. -/
def perm (σ : Equiv.Perm ℕ) : Module.End k (Coeff k) :=
  TensorProduct.map (permK σ).toLinearMap (permCl σ).toLinearMap

@[simp] theorem perm_tmul (σ : Equiv.Perm ℕ) (f : K k) (u : Cl k) :
    perm σ (f ⊗ₜ[k] u) = permK σ f ⊗ₜ[k] permCl σ u := by simp [perm]

theorem scalar_mul (f g : K k) : scalar (f * g) = scalar f * scalar g := by
  apply TensorProduct.ext'; intro h u; simp [mul_assoc]

theorem scalar_add (f g : K k) : scalar (f + g) = scalar f + scalar g := by
  apply TensorProduct.ext'; intro h u; simp [add_mul, TensorProduct.add_tmul]

theorem scalar_sub (f g : K k) : scalar (f - g) = scalar f - scalar g := by
  apply TensorProduct.ext'; intro h u; simp [sub_mul, TensorProduct.sub_tmul]

theorem scalar_neg (f : K k) : scalar (-f) = -scalar f := by
  apply TensorProduct.ext'; intro h u; simp [TensorProduct.neg_tmul]

@[simp] theorem scalar_one : scalar (1 : K k) = 1 := by
  apply TensorProduct.ext'; intro h u; simp

@[simp] theorem scalar_zero : scalar (0 : K k) = 0 := by
  apply TensorProduct.ext'; intro h u; simp

theorem scalar_algebraMap (a : k) : scalar (algebraMap k (K k) a) = a • 1 := by
  apply TensorProduct.ext'; intro h u
  simp [Algebra.smul_def, TensorProduct.smul_tmul']

theorem scalar_commute (f g : K k) : Commute (scalar f) (scalar g) := by
  rw [Commute, SemiconjBy, ← scalar_mul, ← scalar_mul, mul_comm]

theorem cliff_mul_self (p : ℕ) : cliff (k := k) p * cliff p = 1 := by
  apply TensorProduct.ext'; intro f u
  simp [← mul_assoc]

theorem cliff_anticomm {p q : ℕ} (h : p ≠ q) :
    cliff (k := k) p * cliff q = -(cliff q * cliff p) := by
  apply TensorProduct.ext'; intro f u
  simp only [Module.End.mul_apply, cliff_tmul, LinearMap.neg_apply]
  rw [reflect_comm p q f, ← mul_assoc, c_anticomm h, neg_mul, TensorProduct.tmul_neg,
    mul_assoc]

theorem cliff_scalar (p : ℕ) (f : K k) : cliff p * scalar f = scalar (reflect p f) * cliff p := by
  apply TensorProduct.ext'; intro g u; simp

theorem perm_scalar (σ : Equiv.Perm ℕ) (f : K k) :
    perm σ * scalar f = scalar (permK σ f) * perm σ := by
  apply TensorProduct.ext'; intro g u; simp

theorem perm_cliff (σ : Equiv.Perm ℕ) (p : ℕ) :
    perm (k := k) σ * cliff p = cliff (σ p) * perm σ := by
  apply TensorProduct.ext'; intro g u; simp [permK_reflect]

theorem perm_mul (σ τ : Equiv.Perm ℕ) : perm (k := k) (σ * τ) = perm σ * perm τ := by
  apply TensorProduct.ext'; intro g u; simp [permK_mul, permCl_mul]

@[simp] theorem perm_one : perm (k := k) 1 = 1 := by
  apply TensorProduct.ext'; intro g u; simp

end OddMath.QuiverHecke.Realization

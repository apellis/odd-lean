/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CliffordColours

/-!
# Permutation transport of polynomial–Clifford coefficients

The symmetric group permutes the variables, Clifford generators and colours
simultaneously, as required in KKT arXiv:1107.1039v2, §3.4 before Theorem 3.8.
These are coefficient permutations, not the twisted generators of Proposition 3.3.
-/

noncomputable section
open scoped TensorProduct BigOperators nonZeroDivisors
namespace OddMath.QuiverHecke.CliffordPermutations

variable {R : Type*} [CommRing R] {n : ℕ}
open CliffordLocalization CliffordCoefficients

/-- Permutation of localized ordinary polynomial variables. -/
def permK (w : Equiv.Perm (Fin n)) : K R n ≃ₐ[R] K R n :=
  IsFractionRing.algEquivOfAlgEquiv (MvPolynomial.renameEquiv R w)

@[simp] theorem permK_y (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permK (R := R) w (y i) = y (w i) := by
  simp [permK, y, MvPolynomial.renameEquiv]

/-- Coordinate permutations preserve the Clifford quadratic form. -/
def permForm (w : Equiv.Perm (Fin n)) : (form R n).IsometryEquiv (form R n) where
  toLinearEquiv := LinearEquiv.funCongrLeft R R w.symm
  map_app' v := by
    simp only [form, QuadraticMap.weightedSumSquares_apply, smul_eq_mul, one_mul]
    exact Equiv.sum_comp w.symm (fun i => v i * v i)

/-- Induced permutation of Clifford generators. -/
def permCl (w : Equiv.Perm (Fin n)) : Cl R n ≃ₐ[R] Cl R n :=
  CliffordAlgebra.equivOfIsometry (permForm w)

@[simp] theorem permCl_c (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permCl (R := R) w (c R n i) = c R n (w i) := by
  simp only [permCl, c, CliffordAlgebra.equivOfIsometry_apply,
    CliffordAlgebra.map_apply_ι]
  congr 1
  funext j
  change (Pi.single i (1 : R) : Fin n → R) (w.symm j) =
    (Pi.single (w i) 1 : Fin n → R) j
  by_cases h : j = w i
  · subst j; simp
  · have hh : w.symm j ≠ i := by simpa [Equiv.symm_apply_eq] using h
    simp [h, hh]

/-- Localized permutations conjugate coordinate reflections. -/
theorem permK_reflect (w : Equiv.Perm (Fin n)) (i : Fin n) (a : K R n) :
    permK w (reflect i a) = reflect (w i) (permK w a) := by
  have heq : (permK (R := R) w).toAlgHom.comp (reflect i).toAlgHom =
      (reflect (w i)).toAlgHom.comp (permK w).toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (P R n))
    ext j
    change permK w (reflect i (y j)) = reflect (w i) (permK (R := R) w (y j))
    by_cases h : j = i <;> simp [h]
  exact DFunLike.congr_fun heq a

/-- Simultaneous permutation of the two coefficient tensor factors. -/
def permCoeff (w : Equiv.Perm (Fin n)) :
    Module.End R (CliffordLocalization.Coeff (R := R) (n := n)) :=
  TensorProduct.map (permK w).toLinearMap (permCl w).toLinearMap

@[simp] theorem permCoeff_tmul (w : Equiv.Perm (Fin n)) (a : K R n) (v : Cl R n) :
    permCoeff w (a ⊗ₜ[R] v) = permK w a ⊗ₜ[R] permCl w v := by simp [permCoeff]

/-- Permutations transport each localized Clifford operator to its new position. -/
theorem permCoeff_C (w : Equiv.Perm (Fin n)) (i : Fin n) :
    permCoeff (R := R) w * CliffordLocalization.C i =
      CliffordLocalization.C (w i) * permCoeff w := by
  apply TensorProduct.ext'
  intro a v
  simp [Module.End.mul_apply, permK_reflect]

/-- Permutations transport every localized scalar operator. -/
theorem permCoeff_scalar (w : Equiv.Perm (Fin n)) (a : K R n) :
    permCoeff w * CliffordLocalization.scalar a =
      CliffordLocalization.scalar (permK w a) * permCoeff w := by
  apply TensorProduct.ext'
  intro b v
  simp [Module.End.mul_apply]

/-- Localized coefficient permutations respect multiplication in the symmetric group. -/
theorem permK_mul (w v : Equiv.Perm (Fin n)) (a : K R n) :
    permK (w * v) a = permK w (permK v a) := by
  have heq : (permK (R := R) (w * v)).toAlgHom =
      (permK w).toAlgHom.comp (permK v).toAlgHom := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (P R n))
    ext i
    change permK (w * v) (y i) = permK w (permK (R := R) v (y i))
    simp
  exact DFunLike.congr_fun heq a

@[simp] theorem permK_one (a : K R n) : permK 1 a = a := by
  have heq : (permK (R := R) (1 : Equiv.Perm (Fin n))).toAlgHom = AlgHom.id R (K R n) := by
    apply IsLocalization.algHom_ext (nonZeroDivisors (P R n))
    ext i
    change permK 1 (y i) = y (R := R) i
    simp
  exact DFunLike.congr_fun heq a

/-- Clifford coefficient permutations respect symmetric-group multiplication. -/
theorem permCl_mul (w v : Equiv.Perm (Fin n)) (a : Cl R n) :
    permCl (w * v) a = permCl w (permCl v a) := by
  have heq : (permCl (R := R) (w * v)).toAlgHom =
      (permCl w).toAlgHom.comp (permCl v).toAlgHom := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    simp only [AlgHom.comp_toLinearMap, LinearMap.comp_apply]
    change CliffordAlgebra.map _ (CliffordAlgebra.ι _ x) =
      CliffordAlgebra.map _ (CliffordAlgebra.map _ (CliffordAlgebra.ι _ x))
    simp only [CliffordAlgebra.map_apply_ι]
    rfl
  exact DFunLike.congr_fun heq a

@[simp] theorem permCl_one (a : Cl R n) : permCl 1 a = a := by
  have heq : (permCl (R := R) (1 : Equiv.Perm (Fin n))).toAlgHom = AlgHom.id R (Cl R n) := by
    apply CliffordAlgebra.hom_ext
    apply LinearMap.ext
    intro x
    change CliffordAlgebra.map _ (CliffordAlgebra.ι _ x) = CliffordAlgebra.ι _ x
    rw [CliffordAlgebra.map_apply_ι]
    rfl
  exact DFunLike.congr_fun heq a

/-- The tensor coefficient permutations form a symmetric-group action. -/
theorem permCoeff_mul (w v : Equiv.Perm (Fin n)) :
    permCoeff (R := R) (w * v) = permCoeff w * permCoeff v := by
  apply TensorProduct.ext'
  intro a b
  simp [Module.End.mul_apply, permK_mul, permCl_mul]

@[simp] theorem permCoeff_one : permCoeff (R := R) (1 : Equiv.Perm (Fin n)) = 1 := by
  apply TensorProduct.ext'
  intro a b
  simp

open CliffordColours
variable {J : Type*}

/-- Simultaneous permutation of colour words and localized coefficients. -/
def perm (w : Equiv.Perm (Fin n)) : Module.End R (Space R J n) where
  toFun f ν := permCoeff w (f (ν ∘ w))
  map_add' f g := by funext ν; simp
  map_smul' a f := by funext ν; simp

@[simp] theorem perm_apply (w : Equiv.Perm (Fin n)) (f : Space R J n) (ν : Word J n) :
    perm w f ν = permCoeff w (f (ν ∘ w)) := rfl

/-- The simultaneous permutations give an action on colour coefficients. -/
theorem perm_mul (w v : Equiv.Perm (Fin n)) :
    perm (R := R) (J := J) (w * v) = perm w * perm v := by
  apply LinearMap.ext
  intro f
  funext ν
  simp only [Module.End.mul_apply, perm_apply, permCoeff_mul]
  rfl

@[simp] theorem perm_one : perm (R := R) (J := J) (1 : Equiv.Perm (Fin n)) = 1 := by
  apply LinearMap.ext
  intro f
  funext ν
  simp

/-- Colour projections transform by the natural permutation of words. -/
theorem perm_e (w : Equiv.Perm (Fin n)) (ν : Word J n) :
    perm (R := R) w * e ν = e (ν ∘ w.symm) * perm w := by
  classical
  apply LinearMap.ext
  intro f
  funext μ
  have heq : μ ∘ w = ν ↔ μ = ν ∘ w.symm := by
    constructor
    · intro h
      funext i
      simpa using congrFun h (w.symm i)
    · intro h
      subst μ
      funext i
      simp
  simp only [Module.End.mul_apply, perm_apply, e_apply]
  simp only [heq]
  by_cases h : μ = ν ∘ w.symm <;> simp only [h, ite_true, ite_false, map_zero]

/-- Permutations transport colour-coupled Clifford generators. -/
theorem perm_C (w : Equiv.Perm (Fin n)) (c : J → J) (i : Fin n) :
    perm (R := R) w * CliffordColours.C c i =
      CliffordColours.C c (w i) * perm w := by
  apply LinearMap.ext
  intro f
  funext ν
  have hword : flip c i (ν ∘ w) = flip c (w i) ν ∘ w := by
    funext j
    simp [CliffordColours.flip]
  simp only [Module.End.mul_apply, perm_apply, CliffordColours.C_apply, hword]
  exact DFunLike.congr_fun (permCoeff_C w i) (f (CliffordColours.flip c (w i) ν ∘ w))

/-- Permutations transport localized scalar multiplication on all colour summands. -/
theorem perm_scalar (w : Equiv.Perm (Fin n)) (a : K R n) :
    perm (J := J) w * CliffordColours.scalar a =
      CliffordColours.scalar (permK w a) * perm w := by
  apply LinearMap.ext
  intro f
  funext ν
  exact DFunLike.congr_fun (permCoeff_scalar w a) (f (ν ∘ w))

/-- The symmetric-group action on colour-indexed localized Clifford coefficients. -/
def action : Equiv.Perm (Fin n) →* Module.End R (Space R J n) where
  toFun := perm
  map_one' := perm_one
  map_mul' := perm_mul

end OddMath.QuiverHecke.CliffordPermutations

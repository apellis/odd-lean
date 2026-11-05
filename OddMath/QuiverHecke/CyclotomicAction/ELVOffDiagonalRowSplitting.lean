/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalRowDivision
/-!
# The polynomial boundary row in both height ranges

The positive assembly is the original boundary plus literal polynomial-window
inclusion. The negative assembly is the low corrected kernel plus the section
constructed by boundary-row division. Their inverses and the positive cokernel
are proved here. These row results feed the snake and augmented-inverse
arguments; they do not identify the prescribed balanced crossing-column domain.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The positive-height row with its literal polynomial-window columns. -/
def offDiagonalBoundaryPositiveAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    ((ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t).coprod
    (offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype

theorem offDiagonalBoundaryPositiveAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Bijective (offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t) := by
  constructor
  · intro x y hxy
    have hz : offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t (x - y) = 0 := by
      rw [(offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t).map_sub x y, hxy, sub_self]
    change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (x - y).1 + (x - y).2 = 0 at hz
    let q := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm (x - y).1
    have hh := offDiagonalCorrectedBoundaryRow_separation D Sc cutoff p j v t q (x - y).2
      (fun d _ => by omega) (fun n hn => (x - y).2.property hn)
      (by simpa only [q, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hz)
    apply sub_eq_zero.mp
    apply Prod.ext
    · change (x - y).1 = 0
      have he := congrArg (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t) hh.1
      simpa only [q, LinearEquiv.apply_symm_apply, map_zero] using he
    · exact Subtype.ext hh.2
  · intro f
    obtain ⟨q, r, he, _, hr⟩ := offDiagonalCorrectedBoundaryRow_division D Sc cutoff p j v t f
    refine ⟨(offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t q, ⟨r, fun _ hn => hr _ hn⟩), ?_⟩
    exact he

/-- Positive-height direct sum using the original polynomial boundary as its first entry. -/
def offDiagonalBoundaryPositiveEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryPositiveAssembly D Sc cutoff p j v t)
    (offDiagonalBoundaryPositiveAssembly_bijective D Sc cutoff p j v t h)

@[simp] theorem offDiagonalBoundaryPositiveEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v t) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h x =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t x.1 + x.2 := rfl

/-- The low window in corrected source coordinates. -/
def offDiagonalBoundaryKernelWindow (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v}

/-- Inclusion of the low corrected window into the kernel of the original row. -/
def offDiagonalBoundaryKernelInclusion (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    offDiagonalBoundaryKernelWindow D Sc cutoff j v t →ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
  (((offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap).comp
    (offDiagonalBoundaryKernelWindow D Sc cutoff j v t).subtype).codRestrict _ (by
      intro f
      exact (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t f).mpr (fun d hd => f.property hd))

/-- The low corrected window is precisely the kernel, in both directions. -/
def offDiagonalBoundaryKernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    offDiagonalBoundaryKernelWindow D Sc cutoff j v t ≃ₗ[k]
      LinearMap.ker (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryKernelInclusion D Sc cutoff p j v t) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      apply (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).injective
      exact congrArg Subtype.val hfg
    · intro f
      let g := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm f.val
      have hg : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t g = 0 := by
        simpa only [g, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using (LinearMap.mem_ker.mp f.property)
      refine ⟨⟨g, fun d hd => (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t g).mp hg d hd⟩, ?_⟩
      apply Subtype.ext
      change offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t g = f.val
      exact LinearEquiv.apply_symm_apply _ _)

/-- The section obtained by the proved row division, with zero low-source part. -/
def offDiagonalBoundaryRowSection (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap.comp
    ((offDiagonalBoundaryRowHigh D Sc cutoff j v t).subtype.comp
      ((LinearMap.fst k _ _).comp (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).symm.toLinearMap))

theorem offDiagonalBoundaryRowSection_rightInverse (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (offDiagonalBoundaryRowSection D Sc cutoff p j v t f) = f := by
  let x := (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).symm f
  have hx : (x.2 : ℕ →₀ Old D Sc cutoff v t) = 0 := by
    ext n
    by_contra hn
    have hh := x.2.property (Finsupp.mem_support_iff.mpr hn)
    change n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v at hh
    omega
  have he := (offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t).apply_symm_apply f
  rw [offDiagonalBoundaryRowDivisionEquiv_apply] at he
  change offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
    (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t x.1) + x.2 = f at he
  rw [hx, add_zero] at he
  exact he

/-- At height a the remainder is exactly the polynomial window of degrees below a. -/
theorem offDiagonalBoundaryRowWindow_eq_height (j : {j : I // D.parity j = 1}) (v t : List I)
    (a : ℕ) (ha : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + a) :
    offDiagonalBoundaryRowWindow D Sc cutoff j v t =
      Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio a) := by
  unfold offDiagonalBoundaryRowWindow
  congr 1
  ext n
  change (n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) ↔ n < a
  omega

theorem offDiagonalBoundaryPositiveEquiv_symm_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).symm
      (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f) = (f, 0) := by
  apply (offDiagonalBoundaryPositiveEquiv D Sc cutoff p j v t h).injective
  rw [LinearEquiv.apply_symm_apply, offDiagonalBoundaryPositiveEquiv_apply]
  exact (add_zero _).symm

end OddMath.QuiverHecke.ELVOld

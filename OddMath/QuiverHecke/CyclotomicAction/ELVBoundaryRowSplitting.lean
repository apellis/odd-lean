/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowDivision
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
def boundaryPositiveAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    ((ℕ →₀ Old D Sc cutoff v v) × boundaryRowWindow D Sc cutoff j v) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  (outputPolynomialBoundary D Sc cutoff p j v).coprod
    (boundaryRowWindow D Sc cutoff j v).subtype

theorem boundaryPositiveAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Bijective (boundaryPositiveAssembly D Sc cutoff p j v) := by
  constructor
  · intro x y hxy
    have hz : boundaryPositiveAssembly D Sc cutoff p j v (x - y) = 0 := by
      rw [(boundaryPositiveAssembly D Sc cutoff p j v).map_sub x y, hxy, sub_self]
    change outputPolynomialBoundary D Sc cutoff p j v (x - y).1 + (x - y).2 = 0 at hz
    let q := (outputCorrectedCoordinateEquiv D Sc cutoff p j v).symm (x - y).1
    have hh := correctedBoundaryRow_separation D Sc cutoff p j v q (x - y).2
      (fun d _ => by omega) (fun n hn => (x - y).2.property hn)
      (by simpa only [q, correctedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] using hz)
    apply sub_eq_zero.mp
    apply Prod.ext
    · change (x - y).1 = 0
      have he := congrArg (outputCorrectedCoordinateEquiv D Sc cutoff p j v) hh.1
      simpa only [q, LinearEquiv.apply_symm_apply, map_zero] using he
    · exact Subtype.ext hh.2
  · intro f
    obtain ⟨q, r, he, _, hr⟩ := correctedBoundaryRow_division D Sc cutoff p j v f
    refine ⟨(outputCorrectedCoordinateEquiv D Sc cutoff p j v q, ⟨r, fun _ hn => hr _ hn⟩), ?_⟩
    exact he

/-- Positive-height direct sum using the original polynomial boundary as its first entry. -/
def boundaryPositiveEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) × boundaryRowWindow D Sc cutoff j v) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  LinearEquiv.ofBijective (boundaryPositiveAssembly D Sc cutoff p j v)
    (boundaryPositiveAssembly_bijective D Sc cutoff p j v h)

@[simp] theorem boundaryPositiveEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v v) × boundaryRowWindow D Sc cutoff j v) :
    boundaryPositiveEquiv D Sc cutoff p j v h x =
      outputPolynomialBoundary D Sc cutoff p j v x.1 + x.2 := rfl

/-- The low window in corrected source coordinates. -/
def boundaryKernelWindow (j : {j : I // D.parity j = 1}) (v : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.supported (Old D Sc cutoff v v) k
    {d | d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v}

/-- Inclusion of the low corrected window into the kernel of the original row. -/
def boundaryKernelInclusion (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    boundaryKernelWindow D Sc cutoff j v →ₗ[k]
      LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) :=
  (((outputCorrectedCoordinateEquiv D Sc cutoff p j v).toLinearMap).comp
    (boundaryKernelWindow D Sc cutoff j v).subtype).codRestrict _ (by
      intro f
      exact (correctedBoundaryRow_eq_zero_iff D Sc cutoff p j v f).mpr (fun d hd => f.property hd))

/-- The low corrected window is precisely the kernel, in both directions. -/
def boundaryKernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    boundaryKernelWindow D Sc cutoff j v ≃ₗ[k]
      LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) :=
  LinearEquiv.ofBijective (boundaryKernelInclusion D Sc cutoff p j v) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      apply (outputCorrectedCoordinateEquiv D Sc cutoff p j v).injective
      exact congrArg Subtype.val hfg
    · intro f
      let g := (outputCorrectedCoordinateEquiv D Sc cutoff p j v).symm f.val
      have hg : correctedBoundaryRow D Sc cutoff p j v g = 0 := by
        simpa only [g, correctedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply] using (LinearMap.mem_ker.mp f.property)
      refine ⟨⟨g, fun d hd => (correctedBoundaryRow_eq_zero_iff D Sc cutoff p j v g).mp hg d hd⟩, ?_⟩
      apply Subtype.ext
      change outputCorrectedCoordinateEquiv D Sc cutoff p j v g = f.val
      exact LinearEquiv.apply_symm_apply _ _)

/-- The section obtained by the proved row division, with zero low-source part. -/
def boundaryRowSection (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (outputCorrectedCoordinateEquiv D Sc cutoff p j v).toLinearMap.comp
    ((boundaryRowHigh D Sc cutoff j v).subtype.comp
      ((LinearMap.fst k _ _).comp (boundaryRowDivisionEquiv D Sc cutoff p j v).symm.toLinearMap))

theorem boundaryRowSection_rightInverse (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    outputPolynomialBoundary D Sc cutoff p j v (boundaryRowSection D Sc cutoff p j v f) = f := by
  let x := (boundaryRowDivisionEquiv D Sc cutoff p j v).symm f
  have hx : (x.2 : ℕ →₀ Old D Sc cutoff v v) = 0 := by
    ext n
    by_contra hn
    have hh := x.2.property (Finsupp.mem_support_iff.mpr hn)
    change n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v at hh
    omega
  have he := (boundaryRowDivisionEquiv D Sc cutoff p j v).apply_symm_apply f
  rw [boundaryRowDivisionEquiv_apply] at he
  change outputPolynomialBoundary D Sc cutoff p j v
    (outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1) + x.2 = f at he
  rw [hx, add_zero] at he
  exact he

/-- Negative-height reconstruction from a low corrected vector and output polynomial. -/
def boundaryNegativeAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (boundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  ((outputCorrectedCoordinateEquiv D Sc cutoff p j v).toLinearMap.comp
    (boundaryKernelWindow D Sc cutoff j v).subtype).coprod
      (boundaryRowSection D Sc cutoff p j v)

theorem boundaryNegativeAssembly_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : boundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    outputPolynomialBoundary D Sc cutoff p j v
      (boundaryNegativeAssembly D Sc cutoff p j v x) = x.2 := by
  change outputPolynomialBoundary D Sc cutoff p j v
    (outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1 + boundaryRowSection D Sc cutoff p j v x.2) = _
  rw [map_add, boundaryRowSection_rightInverse D Sc cutoff p j v h]
  have hz := (correctedBoundaryRow_eq_zero_iff D Sc cutoff p j v x.1).mpr
    (fun d hd => x.1.property hd)
  change outputPolynomialBoundary D Sc cutoff p j v
    (outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1) = 0 at hz
  rw [hz, zero_add]

theorem boundaryNegativeAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Bijective (boundaryNegativeAssembly D Sc cutoff p j v) := by
  constructor
  · intro x y he
    have hy : x.2 = y.2 := by
      have hh := congrArg (outputPolynomialBoundary D Sc cutoff p j v) he
      simpa only [boundaryNegativeAssembly_boundary D Sc cutoff p j v h] using hh
    apply Prod.ext _ hy
    apply Subtype.ext
    apply (outputCorrectedCoordinateEquiv D Sc cutoff p j v).injective
    change outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1 + boundaryRowSection D Sc cutoff p j v x.2 =
      outputCorrectedCoordinateEquiv D Sc cutoff p j v y.1 + boundaryRowSection D Sc cutoff p j v y.2 at he
    rw [hy] at he
    exact add_right_cancel he
  · intro f
    let g := outputPolynomialBoundary D Sc cutoff p j v f
    have hz : f - boundaryRowSection D Sc cutoff p j v g ∈
        LinearMap.ker (outputPolynomialBoundary D Sc cutoff p j v) := by
      rw [LinearMap.mem_ker, map_sub, boundaryRowSection_rightInverse D Sc cutoff p j v h]
      exact sub_self _
    let z := (boundaryKernelEquiv D Sc cutoff p j v).symm ⟨_, hz⟩
    refine ⟨(z, g), ?_⟩
    have he := congrArg Subtype.val ((boundaryKernelEquiv D Sc cutoff p j v).apply_symm_apply ⟨_, hz⟩)
    change outputCorrectedCoordinateEquiv D Sc cutoff p j v z =
      f - boundaryRowSection D Sc cutoff p j v g at he
    change outputCorrectedCoordinateEquiv D Sc cutoff p j v z + boundaryRowSection D Sc cutoff p j v g = f
    rw [he, sub_add_cancel]

/-- The source splits into its low corrected kernel window and actual output row. -/
def boundaryNegativeEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    (boundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  LinearEquiv.ofBijective (boundaryNegativeAssembly D Sc cutoff p j v)
    (boundaryNegativeAssembly_bijective D Sc cutoff p j v h)

/-- Both components reconstruct the original polynomial source explicitly. -/
theorem boundaryNegativeEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : boundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    boundaryNegativeEquiv D Sc cutoff p j v h x =
      outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1 + boundaryRowSection D Sc cutoff p j v x.2 := rfl

/-- The second coordinate of the negative normal form is exactly A. -/
theorem boundaryNegativeEquiv_symm_snd (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    ((boundaryNegativeEquiv D Sc cutoff p j v h).symm f).2 =
      outputPolynomialBoundary D Sc cutoff p j v f := by
  have he := boundaryNegativeAssembly_boundary D Sc cutoff p j v h
    ((boundaryNegativeEquiv D Sc cutoff p j v h).symm f)
  change outputPolynomialBoundary D Sc cutoff p j v
    (boundaryNegativeEquiv D Sc cutoff p j v h ((boundaryNegativeEquiv D Sc cutoff p j v h).symm f)) = _ at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- At height a the remainder is exactly the polynomial window of degrees below a. -/
theorem boundaryRowWindow_eq_height (j : {j : I // D.parity j = 1}) (v : List I)
    (a : ℕ) (ha : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + a) :
    boundaryRowWindow D Sc cutoff j v =
      Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio a) := by
  unfold boundaryRowWindow
  congr 1
  ext n
  change (n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) ↔ n < a
  omega

/-- At height -m the kernel coordinates are exactly the low corrected window below m. -/
theorem boundaryKernelWindow_eq_height (j : {j : I // D.parity j = 1}) (v : List I)
    (m : ℕ) (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    boundaryKernelWindow D Sc cutoff j v =
      Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio m) := by
  unfold boundaryKernelWindow
  congr 1
  ext d
  change (d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) ↔ d < m
  omega

/-- Actual division remainder, not an independently postulated projection. -/
def boundaryPositiveRemainder (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] boundaryRowWindow D Sc cutoff j v :=
  (LinearMap.snd k _ _).comp (boundaryPositiveEquiv D Sc cutoff p j v h).symm.toLinearMap

theorem boundaryPositiveEquiv_symm_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (boundaryPositiveEquiv D Sc cutoff p j v h).symm
      (outputPolynomialBoundary D Sc cutoff p j v f) = (f, 0) := by
  apply (boundaryPositiveEquiv D Sc cutoff p j v h).injective
  rw [LinearEquiv.apply_symm_apply, boundaryPositiveEquiv_apply]
  exact (add_zero _).symm

theorem boundaryPositiveRemainder_ker (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    LinearMap.ker (boundaryPositiveRemainder D Sc cutoff p j v h) =
      LinearMap.range (outputPolynomialBoundary D Sc cutoff p j v) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    let x := (boundaryPositiveEquiv D Sc cutoff p j v h).symm f
    refine ⟨x.1, ?_⟩
    have he := (boundaryPositiveEquiv D Sc cutoff p j v h).apply_symm_apply f
    rw [boundaryPositiveEquiv_apply] at he
    change outputPolynomialBoundary D Sc cutoff p j v x.1 + x.2 = f at he
    change x.2 = 0 at hf
    simpa only [hf, ZeroMemClass.coe_zero, add_zero] using he
  · rintro ⟨g, rfl⟩
    change ((boundaryPositiveEquiv D Sc cutoff p j v h).symm
      (outputPolynomialBoundary D Sc cutoff p j v g)).2 = 0
    rw [boundaryPositiveEquiv_symm_boundary]

theorem boundaryPositiveRemainder_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Surjective (boundaryPositiveRemainder D Sc cutoff p j v h) := by
  intro r
  refine ⟨boundaryPositiveEquiv D Sc cutoff p j v h (0, r), ?_⟩
  change ((boundaryPositiveEquiv D Sc cutoff p j v h).symm
    (boundaryPositiveEquiv D Sc cutoff p j v h (0, r))).2 = r
  rw [LinearEquiv.symm_apply_apply]

private def rowCokernelEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (r : M →ₗ[R] N) (P : Submodule R M)
    (he : P = LinearMap.ker r) (hs : Function.Surjective r) : (M ⧸ P) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ he).trans (r.quotKerEquivOfSurjective hs)

/-- The cokernel of the prescribed positive row is the actual polynomial window. -/
def boundaryPositiveCokernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) ⧸ LinearMap.range (outputPolynomialBoundary D Sc cutoff p j v)) ≃ₗ[k]
      boundaryRowWindow D Sc cutoff j v :=
  rowCokernelEquiv (R := k) (M := ℕ →₀ Old D Sc cutoff v v)
    (N := boundaryRowWindow D Sc cutoff j v) (boundaryPositiveRemainder D Sc cutoff p j v h)
    (LinearMap.range (outputPolynomialBoundary D Sc cutoff p j v))
    (boundaryPositiveRemainder_ker D Sc cutoff p j v h).symm
    (boundaryPositiveRemainder_surjective D Sc cutoff p j v h)

end OddMath.QuiverHecke.ELVOld

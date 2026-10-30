/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVEvenBoundaryDivision
/-!
# The polynomial boundary row in both height ranges

The positive assembly is the original boundary plus literal polynomial-window
inclusion. The negative assembly is the low kernel plus the section
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
def evenBoundaryPositiveAssembly (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    ((ℕ →₀ Old D Sc cutoff v v) × evenBoundaryRowWindow D Sc cutoff j v) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  (evenPolynomialBoundary D Sc cutoff p j.1 v).coprod
    (evenBoundaryRowWindow D Sc cutoff j v).subtype

theorem evenBoundaryPositiveAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Bijective (evenBoundaryPositiveAssembly D Sc cutoff p j v) := by
  constructor
  · intro x y hxy
    have hz : evenBoundaryPositiveAssembly D Sc cutoff p j v (x - y) = 0 := by
      rw [(evenBoundaryPositiveAssembly D Sc cutoff p j v).map_sub x y, hxy, sub_self]
    change evenPolynomialBoundary D Sc cutoff p j.1 v (x - y).1 + (x - y).2 = 0 at hz
    have hh := evenBoundaryRow_separation D Sc cutoff p j v (x - y).1 (x - y).2
      (fun d _ => by omega) (fun n hn => (x - y).2.property hn) hz
    apply sub_eq_zero.mp
    apply Prod.ext
    · exact hh.1
    · exact Subtype.ext hh.2
  · intro f
    obtain ⟨q, r, he, _, hr⟩ := evenBoundaryRow_division D Sc cutoff p j v f
    refine ⟨(q, ⟨r, fun _ hn => hr _ hn⟩), ?_⟩
    exact he

/-- Positive-height direct sum using the original polynomial boundary as its first entry. -/
def evenBoundaryPositiveEquiv (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) × evenBoundaryRowWindow D Sc cutoff j v) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  LinearEquiv.ofBijective (evenBoundaryPositiveAssembly D Sc cutoff p j v)
    (evenBoundaryPositiveAssembly_bijective D Sc cutoff p j v h)

@[simp] theorem evenBoundaryPositiveEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (x : (ℕ →₀ Old D Sc cutoff v v) × evenBoundaryRowWindow D Sc cutoff j v) :
    evenBoundaryPositiveEquiv D Sc cutoff p j v h x =
      evenPolynomialBoundary D Sc cutoff p j.1 v x.1 + x.2 := rfl

/-- The low window in source coordinates. -/
def evenBoundaryKernelWindow (j : {j : I // D.parity j = 0}) (v : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.supported (Old D Sc cutoff v v) k
    {d | d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v}

/-- Inclusion of the low window into the kernel of the original row. -/
def evenBoundaryKernelInclusion (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    evenBoundaryKernelWindow D Sc cutoff j v →ₗ[k]
      LinearMap.ker (evenPolynomialBoundary D Sc cutoff p j.1 v) :=
  (evenBoundaryKernelWindow D Sc cutoff j v).subtype.codRestrict _ (by
      intro f
      exact (evenBoundaryRow_eq_zero_iff D Sc cutoff p j v f).mpr (fun d hd => f.property hd))

/-- The low window is precisely the kernel, in both directions. -/
def evenBoundaryKernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    evenBoundaryKernelWindow D Sc cutoff j v ≃ₗ[k]
      LinearMap.ker (evenPolynomialBoundary D Sc cutoff p j.1 v) :=
  LinearEquiv.ofBijective (evenBoundaryKernelInclusion D Sc cutoff p j v) (by
    constructor
    · intro f g hfg
      apply Subtype.ext
      have h := congrArg (fun x : LinearMap.ker (evenPolynomialBoundary D Sc cutoff p j.1 v) =>
        (x : ℕ →₀ Old D Sc cutoff v v)) hfg
      exact h
    · intro f
      refine ⟨⟨f.val, fun d hd => (evenBoundaryRow_eq_zero_iff D Sc cutoff p j v f.val).mp
        (LinearMap.mem_ker.mp f.property) d hd⟩, ?_⟩
      rfl)

/-- The section obtained by the proved row division, with zero low-source part. -/
def evenBoundaryRowSection (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (evenBoundaryRowHigh D Sc cutoff j v).subtype.comp
    ((LinearMap.fst k _ _).comp (evenBoundaryRowDivisionEquiv D Sc cutoff p j v).symm.toLinearMap)

theorem evenBoundaryRowSection_rightInverse (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    evenPolynomialBoundary D Sc cutoff p j.1 v (evenBoundaryRowSection D Sc cutoff p j v f) = f := by
  let x := (evenBoundaryRowDivisionEquiv D Sc cutoff p j v).symm f
  have hx : (x.2 : ℕ →₀ Old D Sc cutoff v v) = 0 := by
    ext n
    by_contra hn
    have hh := x.2.property (Finsupp.mem_support_iff.mpr hn)
    change n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v at hh
    omega
  have he := (evenBoundaryRowDivisionEquiv D Sc cutoff p j v).apply_symm_apply f
  rw [evenBoundaryRowDivisionEquiv_apply] at he
  change evenPolynomialBoundary D Sc cutoff p j.1 v
    ((x.1 : ℕ →₀ Old D Sc cutoff v v)) + x.2 = f at he
  rw [hx, add_zero] at he
  exact he

/-- Negative-height reconstruction from a low vector and output polynomial. -/
def evenBoundaryNegativeAssembly (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I) :
    (evenBoundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  (evenBoundaryKernelWindow D Sc cutoff j v).subtype.coprod
      (evenBoundaryRowSection D Sc cutoff p j v)

theorem evenBoundaryNegativeAssembly_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : evenBoundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    evenPolynomialBoundary D Sc cutoff p j.1 v
      (evenBoundaryNegativeAssembly D Sc cutoff p j v x) = x.2 := by
  change evenPolynomialBoundary D Sc cutoff p j.1 v
    ((x.1 : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v x.2) = _
  rw [map_add, evenBoundaryRowSection_rightInverse D Sc cutoff p j v h]
  have hz := (evenBoundaryRow_eq_zero_iff D Sc cutoff p j v x.1).mpr
    (fun d hd => x.1.property hd)
  change evenPolynomialBoundary D Sc cutoff p j.1 v
    ((x.1 : ℕ →₀ Old D Sc cutoff v v)) = 0 at hz
  rw [hz, zero_add]

theorem evenBoundaryNegativeAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Bijective (evenBoundaryNegativeAssembly D Sc cutoff p j v) := by
  constructor
  · intro x y he
    have hy : x.2 = y.2 := by
      have hh := congrArg (evenPolynomialBoundary D Sc cutoff p j.1 v) he
      simpa only [evenBoundaryNegativeAssembly_boundary D Sc cutoff p j v h] using hh
    apply Prod.ext _ hy
    apply Subtype.ext
    change (x.1 : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v x.2 =
      (y.1 : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v y.2 at he
    rw [hy] at he
    exact add_right_cancel he
  · intro f
    let g := evenPolynomialBoundary D Sc cutoff p j.1 v f
    have hz : f - evenBoundaryRowSection D Sc cutoff p j v g ∈
        LinearMap.ker (evenPolynomialBoundary D Sc cutoff p j.1 v) := by
      rw [LinearMap.mem_ker, map_sub, evenBoundaryRowSection_rightInverse D Sc cutoff p j v h]
      exact sub_self _
    let z := (evenBoundaryKernelEquiv D Sc cutoff p j v).symm ⟨_, hz⟩
    refine ⟨(z, g), ?_⟩
    have he := congrArg Subtype.val ((evenBoundaryKernelEquiv D Sc cutoff p j v).apply_symm_apply ⟨_, hz⟩)
    change (z : ℕ →₀ Old D Sc cutoff v v) =
      f - evenBoundaryRowSection D Sc cutoff p j v g at he
    change (z : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v g = f
    rw [he, sub_add_cancel]

/-- The source splits into its low kernel window and actual output row. -/
def evenBoundaryNegativeEquiv (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    (evenBoundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  LinearEquiv.ofBijective (evenBoundaryNegativeAssembly D Sc cutoff p j v)
    (evenBoundaryNegativeAssembly_bijective D Sc cutoff p j v h)

/-- Both components reconstruct the original polynomial source explicitly. -/
theorem evenBoundaryNegativeEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (x : evenBoundaryKernelWindow D Sc cutoff j v × (ℕ →₀ Old D Sc cutoff v v)) :
    evenBoundaryNegativeEquiv D Sc cutoff p j v h x =
      (x.1 : ℕ →₀ Old D Sc cutoff v v) + evenBoundaryRowSection D Sc cutoff p j v x.2 := rfl

/-- The second coordinate of the negative normal form is exactly A. -/
theorem evenBoundaryNegativeEquiv_symm_snd (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    ((evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm f).2 =
      evenPolynomialBoundary D Sc cutoff p j.1 v f := by
  have he := evenBoundaryNegativeAssembly_boundary D Sc cutoff p j v h
    ((evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm f)
  change evenPolynomialBoundary D Sc cutoff p j.1 v
    (evenBoundaryNegativeEquiv D Sc cutoff p j v h ((evenBoundaryNegativeEquiv D Sc cutoff p j v h).symm f)) = _ at he
  rw [LinearEquiv.apply_symm_apply] at he
  exact he.symm

/-- At height a the remainder is exactly the polynomial window of degrees below a. -/
theorem evenBoundaryRowWindow_eq_height (j : {j : I // D.parity j = 0}) (v : List I)
    (a : ℕ) (ha : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + a) :
    evenBoundaryRowWindow D Sc cutoff j v =
      Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio a) := by
  unfold evenBoundaryRowWindow
  congr 1
  ext n
  change (n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) ↔ n < a
  omega

/-- At height -m the kernel coordinates are exactly the low window below m. -/
theorem evenBoundaryKernelWindow_eq_height (j : {j : I // D.parity j = 0}) (v : List I)
    (m : ℕ) (hm : outputSDegree D j.1 v = endpointQPDegree D cutoff j.1 v + m) :
    evenBoundaryKernelWindow D Sc cutoff j v =
      Finsupp.supported (Old D Sc cutoff v v) k (Set.Iio m) := by
  unfold evenBoundaryKernelWindow
  congr 1
  ext d
  change (d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v) ↔ d < m
  omega

/-- Actual division remainder, not an independently postulated projection. -/
def evenBoundaryPositiveRemainder (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] evenBoundaryRowWindow D Sc cutoff j v :=
  (LinearMap.snd k _ _).comp (evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm.toLinearMap

theorem evenBoundaryPositiveEquiv_symm_boundary (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    (evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm
      (evenPolynomialBoundary D Sc cutoff p j.1 v f) = (f, 0) := by
  apply (evenBoundaryPositiveEquiv D Sc cutoff p j v h).injective
  rw [LinearEquiv.apply_symm_apply, evenBoundaryPositiveEquiv_apply]
  exact (add_zero _).symm

theorem evenBoundaryPositiveRemainder_ker (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    LinearMap.ker (evenBoundaryPositiveRemainder D Sc cutoff p j v h) =
      LinearMap.range (evenPolynomialBoundary D Sc cutoff p j.1 v) := by
  ext f
  rw [LinearMap.mem_ker, LinearMap.mem_range]
  constructor
  · intro hf
    let x := (evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm f
    refine ⟨x.1, ?_⟩
    have he := (evenBoundaryPositiveEquiv D Sc cutoff p j v h).apply_symm_apply f
    rw [evenBoundaryPositiveEquiv_apply] at he
    change evenPolynomialBoundary D Sc cutoff p j.1 v x.1 + x.2 = f at he
    change x.2 = 0 at hf
    simpa only [hf, ZeroMemClass.coe_zero, add_zero] using he
  · rintro ⟨g, rfl⟩
    change ((evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm
      (evenPolynomialBoundary D Sc cutoff p j.1 v g)).2 = 0
    rw [evenBoundaryPositiveEquiv_symm_boundary]

theorem evenBoundaryPositiveRemainder_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Surjective (evenBoundaryPositiveRemainder D Sc cutoff p j v h) := by
  intro r
  refine ⟨evenBoundaryPositiveEquiv D Sc cutoff p j v h (0, r), ?_⟩
  change ((evenBoundaryPositiveEquiv D Sc cutoff p j v h).symm
    (evenBoundaryPositiveEquiv D Sc cutoff p j v h (0, r))).2 = r
  rw [LinearEquiv.symm_apply_apply]

private def rowCokernelEquiv {R M N : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (r : M →ₗ[R] N) (P : Submodule R M)
    (he : P = LinearMap.ker r) (hs : Function.Surjective r) : (M ⧸ P) ≃ₗ[R] N :=
  (Submodule.quotEquivOfEq _ _ he).trans (r.quotKerEquivOfSurjective hs)

/-- The cokernel of the prescribed positive row is the actual polynomial window. -/
def evenBoundaryPositiveCokernelEquiv (p : ZMod 2) (j : {j : I // D.parity j = 0}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    ((ℕ →₀ Old D Sc cutoff v v) ⧸ LinearMap.range (evenPolynomialBoundary D Sc cutoff p j.1 v)) ≃ₗ[k]
      evenBoundaryRowWindow D Sc cutoff j v :=
  rowCokernelEquiv (R := k) (M := ℕ →₀ Old D Sc cutoff v v)
    (N := evenBoundaryRowWindow D Sc cutoff j v) (evenBoundaryPositiveRemainder D Sc cutoff p j v h)
    (LinearMap.range (evenPolynomialBoundary D Sc cutoff p j.1 v))
    (evenBoundaryPositiveRemainder_ker D Sc cutoff p j v h).symm
    (evenBoundaryPositiveRemainder_surjective D Sc cutoff p j v h)

end OddMath.QuiverHecke.ELVOld

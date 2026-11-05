/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.DegreeShiftRowDivision
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalBoundaryLeading
import OddMath.QuiverHecke.CyclotomicAction.ELVOffDiagonalCorrectedCoordinates
/-!
# Division and windows on arbitrary old Hom coefficients

Finite elimination uses the actual corrected-coordinate equivalence and the
proved leading maps on Old(v,t), retaining full exterior coefficients.
The resulting row normal forms feed the arbitrary-Hom snake argument.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial boundary in its proved corrected source coordinates. -/
def offDiagonalCorrectedBoundaryRow (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (ℕ →₀ Old D Sc cutoff v t) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t).comp
    (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).toLinearMap

@[simp] theorem offDiagonalCorrectedBoundaryRow_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (d : ℕ) (c : Old D Sc cutoff v t) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t (Finsupp.single d c) =
    offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
      (offDiagonalLongExtraction D Sc cutoff p j.1 v t (offDiagonalCorrectedLift D Sc cutoff p j v t d c)) := by
  simp only [offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
    offDiagonalCorrectedCoordinateEquiv_single]

/-- Exact low-window kernel, with the height difference left untruncated. -/
theorem offDiagonalCorrectedBoundaryRow_eq_zero_iff (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v := by
  exact OddMath.Algebra.DegreeShiftRow.eq_zero_iff (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) f

/-- In nonnegative height the polynomial boundary is injective. -/
theorem offDiagonalPolynomialBoundary_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) := by
  intro f g hfg
  have hf : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (f - g) = 0 := by
    have hs : offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t (f - g) =
        offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t f -
          offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t g :=
      map_sub (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) f g
    exact hs.trans (sub_eq_zero.mpr hfg)
  let q := (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t).symm (f - g)
  have hq : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q = 0 := by
    simpa only [q, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hf
  have hb := (offDiagonalCorrectedBoundaryRow_eq_zero_iff D Sc cutoff p j v t q).mp hq
  have hq0 : q = 0 := by
    ext d
    by_contra hd
    have := hb d (Finsupp.mem_support_iff.mpr hd)
    omega
  have he := congrArg (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t) hq0
  apply sub_eq_zero.mp
  simpa only [q, LinearEquiv.apply_symm_apply, map_zero] using he

/-- Finite division by the boundary row. Quotients have no low-kernel coefficients. -/
theorem offDiagonalCorrectedBoundaryRow_division (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    ∃ q r : ℕ →₀ Old D Sc cutoff v t,
      offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = f ∧
      (∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) ∧
      (∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) := by
  exact OddMath.Algebra.DegreeShiftRow.division (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) f

/-- A high corrected input cannot map into the low output window. -/
theorem offDiagonalCorrectedBoundaryRow_separation (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (q r : ℕ →₀ Old D Sc cutoff v t)
    (hq : ∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v)
    (hr : ∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v)
    (h : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = 0) : q = 0 ∧ r = 0 := by
  exact OddMath.Algebra.DegreeShiftRow.separation (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) q r hq hr h

/-- The allowed corrected-source quotient coefficients. -/
def offDiagonalBoundaryRowHigh (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {d | outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v}

/-- The literal polynomial output window below the nonnegative height. -/
def offDiagonalBoundaryRowWindow (j : {j : I // D.parity j = 1}) (v t : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v t) :=
  Finsupp.supported (Old D Sc cutoff v t) k
    {n | n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v}

/-- The forward division map uses the boundary itself and literal window inclusion. -/
def offDiagonalBoundaryRowAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  ((offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t).comp (offDiagonalBoundaryRowHigh D Sc cutoff j v t).subtype).coprod
    (offDiagonalBoundaryRowWindow D Sc cutoff j v t).subtype

theorem offDiagonalBoundaryRowAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) :
    Function.Bijective (offDiagonalBoundaryRowAssembly D Sc cutoff p j v t) := by
  exact OddMath.Algebra.DegreeShiftRow.assembly_bijective (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t)
    (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t) (outputSDegree D j.1 v) (endpointQPDegree D cutoff j.1 v)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n b hn)
    (by
      intro d n b hn
      rw [offDiagonalCorrectedBoundaryRow_single]
      exact offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n b hn) 

/-- Unique polynomial-row division in both height ranges. -/
def offDiagonalBoundaryRowDivisionEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v t : List I) :
    (offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v t) :=
  LinearEquiv.ofBijective (offDiagonalBoundaryRowAssembly D Sc cutoff p j v t)
    (offDiagonalBoundaryRowAssembly_bijective D Sc cutoff p j v t)

/-- The normal form reconstructs with the prescribed row, not a surrogate map. -/
theorem offDiagonalBoundaryRowDivisionEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (x : offDiagonalBoundaryRowHigh D Sc cutoff j v t × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :
    offDiagonalBoundaryRowDivisionEquiv D Sc cutoff p j v t x =
      offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t
        (offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t x.1) + x.2 := rfl

end OddMath.QuiverHecke.ELVOld

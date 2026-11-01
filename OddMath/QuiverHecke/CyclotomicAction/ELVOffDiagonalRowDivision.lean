/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
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

/-- All source terms strictly below a pivot have zero coefficient at that pivot. -/
theorem offDiagonalCorrectedBoundaryRow_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) (n : ℕ)
    (hf : ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < n + outputSDegree D j.1 v) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t f n = 0 := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [offDiagonalCorrectedBoundaryRow_single]
  exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n (f d) (hf d hd)

/-- The maximal corrected coefficient is detected by the invertible leading map. -/
theorem offDiagonalCorrectedBoundaryRow_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) (d n : ℕ)
    (hf : ∀ e ∈ f.support, e ≤ d)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t f n = offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t n (f d) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single d]
  · rw [offDiagonalCorrectedBoundaryRow_single, offDiagonalBoundary_corrected_top D Sc cutoff p j v t d n _ hn]
  · intro e he hne
    rw [offDiagonalCorrectedBoundaryRow_single]
    exact offDiagonalBoundary_corrected_above D Sc cutoff p j v t e n (f e) (by have := hf e he; omega)
  · intro hd
    rw [Finsupp.notMem_support_iff.mp hd, Finsupp.single_zero, map_zero, Finsupp.zero_apply]

/-- Exact low-window kernel, with the height difference left untruncated. -/
theorem offDiagonalCorrectedBoundaryRow_eq_zero_iff (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (f : ℕ →₀ Old D Sc cutoff v t) :
    offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v := by
  constructor
  · intro hz d hd
    by_contra h
    obtain ⟨e, he, hmax⟩ := f.support.exists_max_image id ⟨d, hd⟩
    have hde : d ≤ e := hmax d hd
    have hn : e + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v +
        outputSDegree D j.1 v = e + endpointQPDegree D cutoff j.1 v := by omega
    have ht := offDiagonalCorrectedBoundaryRow_top D Sc cutoff p j v t f e _ hmax hn
    rw [hz, Finsupp.zero_apply] at ht
    have hc : f e = 0 := (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t _).injective
      (ht.symm.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp he hc
  · intro hf
    ext n
    exact offDiagonalCorrectedBoundaryRow_above D Sc cutoff p j v t f n (fun d hd => by have := hf d hd; omega)

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
  suffices hb : ∀ N (g : ℕ →₀ Old D Sc cutoff v t), (∀ n, N ≤ n → g n = 0) →
      ∃ q r : ℕ →₀ Old D Sc cutoff v t,
        offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = g ∧
        (∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) ∧
        (∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) by
    apply hb (f.support.sup id + 1) f
    intro n hn
    apply Finsupp.notMem_support_iff.mp
    intro hh
    have hh' : n ≤ f.support.sup id := Finset.le_sup (f := id) hh
    omega
  intro N
  induction N with
  | zero =>
    intro g hg
    have hz : g = 0 := by ext n; exact hg n (Nat.zero_le n)
    exact ⟨0, 0, by rw [map_zero, add_zero, hz], by simp, by simp⟩
  | succ N ih =>
    intro g hg
    by_cases hN : N + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v
    · refine ⟨0, g, by rw [map_zero, zero_add], by simp, ?_⟩
      intro n hn
      have hnN : n ≤ N := by
        by_contra h
        exact (Finsupp.mem_support_iff.mp hn) (hg n (by omega))
      omega
    · let d := N + outputSDegree D j.1 v - endpointQPDegree D cutoff j.1 v
      have hd : N + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v := by
        dsimp [d]; omega
      let c := (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t N).symm (g N)
      let s := Finsupp.single d c
      have ht : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t s N = g N := by
        rw [offDiagonalCorrectedBoundaryRow_single, offDiagonalBoundary_corrected_top D Sc cutoff p j v t d N c hd]
        exact LinearEquiv.apply_symm_apply _ _
      have hlow : ∀ n, N ≤ n → (g - offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t s) n = 0 := by
        intro n hn
        by_cases he : n = N
        · subst n; simp only [Finsupp.sub_apply, ht, sub_self]
        · rw [Finsupp.sub_apply, hg n (by omega), offDiagonalCorrectedBoundaryRow_single,
            offDiagonalBoundary_corrected_above D Sc cutoff p j v t d n c (by omega), sub_self]
      obtain ⟨q, r, hqr, hq, hr⟩ := ih _ hlow
      refine ⟨q + s, r, ?_, ?_, hr⟩
      · rw [map_add]
        calc
          _ = (offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r) +
              offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t s := by abel
          _ = g := by rw [hqr]; abel
      · intro e he
        rcases Finset.mem_union.mp (Finsupp.support_add he) with he | he
        · exact hq e he
        · have heq : e = d := by
            by_contra hh
            exact (Finsupp.mem_support_iff.mp he) (Finsupp.single_eq_of_ne hh)
          omega

/-- A high corrected input cannot map into the low output window. -/
theorem offDiagonalCorrectedBoundaryRow_separation (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I) (q r : ℕ →₀ Old D Sc cutoff v t)
    (hq : ∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v)
    (hr : ∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v)
    (h : offDiagonalCorrectedBoundaryRow D Sc cutoff p j v t q + r = 0) : q = 0 ∧ r = 0 := by
  have hq0 : q = 0 := by
    by_contra hq0
    obtain ⟨d, hd, hmax⟩ := q.support.exists_max_image id (Finsupp.support_nonempty_iff.mpr hq0)
    have hd' := hq d hd
    let n := d + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v
    have hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v := by
      dsimp [n]; omega
    have hr0 : r n = 0 := by
      by_contra hh
      have := hr n (Finsupp.mem_support_iff.mpr hh)
      omega
    have hh := congrArg (fun f : ℕ →₀ Old D Sc cutoff v t => f n) h
    rw [Finsupp.add_apply, hr0, add_zero, Finsupp.zero_apply,
      offDiagonalCorrectedBoundaryRow_top D Sc cutoff p j v t q d n hmax hn] at hh
    have hc : q d = 0 := (offDiagonalBoundaryLeadingEquiv D Sc cutoff p j v t n).injective
      (hh.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp hd hc
  refine ⟨hq0, ?_⟩
  simpa only [hq0, map_zero, zero_add] using h

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
  constructor
  · intro x y hxy
    have hz : offDiagonalBoundaryRowAssembly D Sc cutoff p j v t (x - y) = 0 := by
      rw [(offDiagonalBoundaryRowAssembly D Sc cutoff p j v t).map_sub x y, hxy, sub_self]
    have hh := offDiagonalCorrectedBoundaryRow_separation D Sc cutoff p j v t (x - y).1 (x - y).2
      (fun d hd => (x - y).1.property hd) (fun n hn => (x - y).2.property hn) hz
    apply sub_eq_zero.mp
    apply Prod.ext <;> apply Subtype.ext
    · exact hh.1
    · exact hh.2
  · intro f
    obtain ⟨q, r, he, hq, hr⟩ := offDiagonalCorrectedBoundaryRow_division D Sc cutoff p j v t f
    exact ⟨(⟨q, fun _ hd => hq _ hd⟩, ⟨r, fun _ hn => hr _ hn⟩), he⟩

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

/-- In nonpositive height the polynomial boundary is surjective. -/
theorem offDiagonalPolynomialBoundary_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v t : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Surjective (offDiagonalPolynomialBoundary D Sc cutoff p j.1 v t) := by
  intro f
  obtain ⟨q, r, he, _, hr⟩ := offDiagonalCorrectedBoundaryRow_division D Sc cutoff p j v t f
  have hr0 : r = 0 := by
    ext n
    by_contra hh
    have := hr n (Finsupp.mem_support_iff.mpr hh)
    omega
  refine ⟨offDiagonalCorrectedCoordinateEquiv D Sc cutoff p j v t q, ?_⟩
  simpa only [hr0, add_zero, offDiagonalCorrectedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe] using he

end OddMath.QuiverHecke.ELVOld

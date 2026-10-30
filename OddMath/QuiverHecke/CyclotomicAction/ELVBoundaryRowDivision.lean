/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVBoundaryRowLeading
/-!
# Division and windows for the polynomial boundary row

Finite degree elimination uses the proved coefficient leading equivalences
of the boundary itself. The resulting direct-sum equivalence is the row
input to the snake-sequence argument, not an inverse of a balanced column.
-/
noncomputable section
namespace OddMath.QuiverHecke.ELVOld
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial boundary in its proved corrected source coordinates. -/
def correctedBoundaryRow (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (ℕ →₀ Old D Sc cutoff v v) →ₗ[k] (ℕ →₀ Old D Sc cutoff v v) :=
  (outputPolynomialBoundary D Sc cutoff p j v).comp
    (outputCorrectedCoordinateEquiv D Sc cutoff p j v).toLinearMap

@[simp] theorem correctedBoundaryRow_single (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (d : ℕ) (c : Old D Sc cutoff v v) :
    correctedBoundaryRow D Sc cutoff p j v (Finsupp.single d c) =
    outputPolynomialBoundary D Sc cutoff p j v
      (outputLongExtraction D Sc cutoff p j.1 v (outputCorrectedLift D Sc cutoff p j v d c)) := by
  simp only [correctedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
    outputCorrectedCoordinateEquiv_single]

/-- All source terms strictly below a pivot have zero coefficient at that pivot. -/
theorem correctedBoundaryRow_above (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (n : ℕ)
    (hf : ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < n + outputSDegree D j.1 v) :
    correctedBoundaryRow D Sc cutoff p j v f n = 0 := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [correctedBoundaryRow_single]
  exact outputBoundary_corrected_above D Sc cutoff p j v d n (f d) (hf d hd)

/-- The maximal corrected coefficient is detected by the invertible leading map. -/
theorem correctedBoundaryRow_top (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) (d n : ℕ)
    (hf : ∀ e ∈ f.support, e ≤ d)
    (hn : n + outputSDegree D j.1 v = d + endpointQPDegree D cutoff j.1 v) :
    correctedBoundaryRow D Sc cutoff p j v f n = outputBoundaryLeadingEquiv D Sc cutoff p j v n (f d) := by
  conv_lhs => rw [← Finsupp.sum_single f]
  simp only [Finsupp.sum, map_sum, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single d]
  · rw [correctedBoundaryRow_single, outputBoundary_corrected_top D Sc cutoff p j v d n _ hn]
  · intro e he hne
    rw [correctedBoundaryRow_single]
    exact outputBoundary_corrected_above D Sc cutoff p j v e n (f e) (by have := hf e he; omega)
  · intro hd
    rw [Finsupp.notMem_support_iff.mp hd, Finsupp.single_zero, map_zero, Finsupp.zero_apply]

/-- Exact low-window kernel, with the height difference left untruncated. -/
theorem correctedBoundaryRow_eq_zero_iff (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) :
    correctedBoundaryRow D Sc cutoff p j v f = 0 ↔
      ∀ d ∈ f.support, d + endpointQPDegree D cutoff j.1 v < outputSDegree D j.1 v := by
  constructor
  · intro hz d hd
    by_contra h
    obtain ⟨e, he, hmax⟩ := f.support.exists_max_image id ⟨d, hd⟩
    have hde : d ≤ e := hmax d hd
    have hn : e + endpointQPDegree D cutoff j.1 v - outputSDegree D j.1 v +
        outputSDegree D j.1 v = e + endpointQPDegree D cutoff j.1 v := by omega
    have ht := correctedBoundaryRow_top D Sc cutoff p j v f e _ hmax hn
    rw [hz, Finsupp.zero_apply] at ht
    have hc : f e = 0 := (outputBoundaryLeadingEquiv D Sc cutoff p j v _).injective
      (ht.symm.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp he hc
  · intro hf
    ext n
    exact correctedBoundaryRow_above D Sc cutoff p j v f n (fun d hd => by have := hf d hd; omega)

/-- In nonnegative height the polynomial boundary is injective. -/
theorem outputPolynomialBoundary_injective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : outputSDegree D j.1 v ≤ endpointQPDegree D cutoff j.1 v) :
    Function.Injective (outputPolynomialBoundary D Sc cutoff p j v) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro f hf
  let g := (outputCorrectedCoordinateEquiv D Sc cutoff p j v).symm f
  have hg : correctedBoundaryRow D Sc cutoff p j v g = 0 := by
    simpa only [g, correctedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using hf
  have hb := (correctedBoundaryRow_eq_zero_iff D Sc cutoff p j v g).mp hg
  have hg0 : g = 0 := by
    ext d
    by_contra hd
    have := hb d (Finsupp.mem_support_iff.mpr hd)
    omega
  have he := congrArg (outputCorrectedCoordinateEquiv D Sc cutoff p j v) hg0
  simpa only [g, LinearEquiv.apply_symm_apply, map_zero] using he

/-- Finite division by the boundary row. Quotients have no low-kernel coefficients. -/
theorem correctedBoundaryRow_division (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (f : ℕ →₀ Old D Sc cutoff v v) :
    ∃ q r : ℕ →₀ Old D Sc cutoff v v,
      correctedBoundaryRow D Sc cutoff p j v q + r = f ∧
      (∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v) ∧
      (∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v) := by
  suffices hb : ∀ N (g : ℕ →₀ Old D Sc cutoff v v), (∀ n, N ≤ n → g n = 0) →
      ∃ q r : ℕ →₀ Old D Sc cutoff v v,
        correctedBoundaryRow D Sc cutoff p j v q + r = g ∧
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
      let c := (outputBoundaryLeadingEquiv D Sc cutoff p j v N).symm (g N)
      let s := Finsupp.single d c
      have ht : correctedBoundaryRow D Sc cutoff p j v s N = g N := by
        rw [correctedBoundaryRow_single, outputBoundary_corrected_top D Sc cutoff p j v d N c hd]
        exact LinearEquiv.apply_symm_apply _ _
      have hlow : ∀ n, N ≤ n → (g - correctedBoundaryRow D Sc cutoff p j v s) n = 0 := by
        intro n hn
        by_cases he : n = N
        · subst n; simp only [Finsupp.sub_apply, ht, sub_self]
        · rw [Finsupp.sub_apply, hg n (by omega), correctedBoundaryRow_single,
            outputBoundary_corrected_above D Sc cutoff p j v d n c (by omega), sub_self]
      obtain ⟨q, r, hqr, hq, hr⟩ := ih _ hlow
      refine ⟨q + s, r, ?_, ?_, hr⟩
      · rw [map_add]
        calc
          _ = (correctedBoundaryRow D Sc cutoff p j v q + r) +
              correctedBoundaryRow D Sc cutoff p j v s := by abel
          _ = g := by rw [hqr]; abel
      · intro e he
        rcases Finset.mem_union.mp (Finsupp.support_add he) with he | he
        · exact hq e he
        · have heq : e = d := by
            by_contra hh
            exact (Finsupp.mem_support_iff.mp he) (Finsupp.single_eq_of_ne hh)
          omega

/-- A high corrected input cannot map into the low output window. -/
theorem correctedBoundaryRow_separation (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) (q r : ℕ →₀ Old D Sc cutoff v v)
    (hq : ∀ d ∈ q.support, outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v)
    (hr : ∀ n ∈ r.support, n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v)
    (h : correctedBoundaryRow D Sc cutoff p j v q + r = 0) : q = 0 ∧ r = 0 := by
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
    have hh := congrArg (fun f : ℕ →₀ Old D Sc cutoff v v => f n) h
    rw [Finsupp.add_apply, hr0, add_zero, Finsupp.zero_apply,
      correctedBoundaryRow_top D Sc cutoff p j v q d n hmax hn] at hh
    have hc : q d = 0 := (outputBoundaryLeadingEquiv D Sc cutoff p j v n).injective
      (hh.trans (map_zero _).symm)
    exact Finsupp.mem_support_iff.mp hd hc
  refine ⟨hq0, ?_⟩
  simpa only [hq0, map_zero, zero_add] using h

/-- The allowed corrected-source quotient coefficients. -/
def boundaryRowHigh (j : {j : I // D.parity j = 1}) (v : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.supported (Old D Sc cutoff v v) k
    {d | outputSDegree D j.1 v ≤ d + endpointQPDegree D cutoff j.1 v}

/-- The literal polynomial output window below the nonnegative height. -/
def boundaryRowWindow (j : {j : I // D.parity j = 1}) (v : List I) :
    Submodule k (ℕ →₀ Old D Sc cutoff v v) :=
  Finsupp.supported (Old D Sc cutoff v v) k
    {n | n + outputSDegree D j.1 v < endpointQPDegree D cutoff j.1 v}

/-- The forward division map uses the boundary itself and literal window inclusion. -/
def boundaryRowAssembly (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (boundaryRowHigh D Sc cutoff j v × boundaryRowWindow D Sc cutoff j v) →ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  ((correctedBoundaryRow D Sc cutoff p j v).comp (boundaryRowHigh D Sc cutoff j v).subtype).coprod
    (boundaryRowWindow D Sc cutoff j v).subtype

theorem boundaryRowAssembly_bijective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I) :
    Function.Bijective (boundaryRowAssembly D Sc cutoff p j v) := by
  constructor
  · intro x y hxy
    have hz : boundaryRowAssembly D Sc cutoff p j v (x - y) = 0 := by
      rw [(boundaryRowAssembly D Sc cutoff p j v).map_sub x y, hxy, sub_self]
    have hh := correctedBoundaryRow_separation D Sc cutoff p j v (x - y).1 (x - y).2
      (fun d hd => (x - y).1.property hd) (fun n hn => (x - y).2.property hn) hz
    apply sub_eq_zero.mp
    apply Prod.ext <;> apply Subtype.ext
    · exact hh.1
    · exact hh.2
  · intro f
    obtain ⟨q, r, he, hq, hr⟩ := correctedBoundaryRow_division D Sc cutoff p j v f
    exact ⟨(⟨q, fun _ hd => hq _ hd⟩, ⟨r, fun _ hn => hr _ hn⟩), he⟩

/-- Unique polynomial-row division in both height ranges. -/
def boundaryRowDivisionEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1}) (v : List I) :
    (boundaryRowHigh D Sc cutoff j v × boundaryRowWindow D Sc cutoff j v) ≃ₗ[k]
      (ℕ →₀ Old D Sc cutoff v v) :=
  LinearEquiv.ofBijective (boundaryRowAssembly D Sc cutoff p j v)
    (boundaryRowAssembly_bijective D Sc cutoff p j v)

/-- The normal form reconstructs with the prescribed row, not a surrogate map. -/
theorem boundaryRowDivisionEquiv_apply (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (x : boundaryRowHigh D Sc cutoff j v × boundaryRowWindow D Sc cutoff j v) :
    boundaryRowDivisionEquiv D Sc cutoff p j v x =
      outputPolynomialBoundary D Sc cutoff p j v
        (outputCorrectedCoordinateEquiv D Sc cutoff p j v x.1) + x.2 := rfl

/-- In nonpositive height the polynomial boundary is surjective. -/
theorem outputPolynomialBoundary_surjective (p : ZMod 2)
    (j : {j : I // D.parity j = 1}) (v : List I)
    (h : endpointQPDegree D cutoff j.1 v ≤ outputSDegree D j.1 v) :
    Function.Surjective (outputPolynomialBoundary D Sc cutoff p j v) := by
  intro f
  obtain ⟨q, r, he, _, hr⟩ := correctedBoundaryRow_division D Sc cutoff p j v f
  have hr0 : r = 0 := by
    ext n
    by_contra hh
    have := hr n (Finsupp.mem_support_iff.mpr hh)
    omega
  refine ⟨outputCorrectedCoordinateEquiv D Sc cutoff p j v q, ?_⟩
  simpa only [hr0, add_zero, correctedBoundaryRow, LinearMap.comp_apply, LinearEquiv.coe_coe] using he

end OddMath.QuiverHecke.ELVOld

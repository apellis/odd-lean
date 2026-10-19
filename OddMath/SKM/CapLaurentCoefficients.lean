/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.CapFamilyCoefficients
import OddMath.CoveringQuantum.PreF.DotSeries
import Mathlib.RingTheory.LaurentSeries

/-! Laurent coefficient interpretation of the cap class in BE2,
arXiv:1701.04133v2, Theorem 10.3 Claim 5. Only the shorter-word
coefficient equality is assumed; the cap contribution is computed from
the constructed finite decorated-family fibers. This does not prove
the other two matching classes or the whole Claim 5. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators LaurentSeries
open CoveringQuantum.PreF.DotSeries

/-- The geometric dot factor has the expected coefficient at each dot degree. -/
theorem laurent_factor_coeff (β : ℚ) (v : ℕ) (hv : v ≠ 0) (n : ℕ) :
    (factor β v hv : LaurentSeries ℚ).coeff ((v : ℤ) * n) = β ^ n := by
  rw [← Nat.cast_mul, LaurentSeries.coeff_coe_powerSeries, coeff_factor]
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hv)]

/-- Every nonzero geometric-factor coefficient comes from a nonnegative dot count. -/
theorem laurent_factor_support (β : ℚ) (v : ℕ) (hv : v ≠ 0) (z : ℤ)
    (hz : (factor β v hv : LaurentSeries ℚ).coeff z ≠ 0) :
    ∃ n : ℕ, z = (v : ℤ) * n := by
  have hnonneg : 0 ≤ z := by
    by_contra h
    have hh : z ∉ Set.range (Nat.castOrderEmbedding (α := ℤ)) := by
      rintro ⟨n, rfl⟩
      exact h (Int.natCast_nonneg n)
    exact hz (HahnSeries.embDomain_of_notMem_range hh)
  lift z to ℕ using hnonneg with m
  rw [LaurentSeries.coeff_coe_powerSeries, coeff_factor] at hz
  have hd : v ∣ m := by
    by_contra h
    simp [h] at hz
  obtain ⟨n, rfl⟩ := hd
  exact ⟨n, by simp⟩

/-- A finite affine fiber supplies all convolution indices: outside its
first-coordinate image the shorter coefficient vanishes by `hIH`.
The hypothesis `hIH` is precisely a shorter-series coefficient equality,
not an identity for the cap family or an assumed cutoff. -/
theorem affine_fibre_laurent_coeff {K : Type*} (e : K → ℤ) (w : K → ℚ)
    (δ : ℤ) (v : ℕ) (hv : v ≠ 0) (β c : ℚ) (z : ℤ)
    (hg : Set.Finite {u : ℕ × K | e u.2 + δ + (v : ℤ) * u.1 = z})
    (he : ∀ k : ℤ, Set.Finite {u | e u = k}) (L : LaurentSeries ℚ)
    (hIH : ∀ k, (∑ u ∈ (he k).toFinset, w u) = L.coeff k) :
    c * (∑ n ∈ hg.toFinset.image Prod.fst,
      β ^ n * ∑ u ∈ (he (z - δ - (v : ℤ) * n)).toFinset, w u) =
      (HahnSeries.single δ c * (factor β v hv : LaurentSeries ℚ) * L).coeff z := by
  classical
  rw [mul_assoc, HahnSeries.coeff_single_mul]
  congr 1
  simp only [hIH]
  let S := hg.toFinset.image Prod.fst
  let f := fun n : ℕ => ((v : ℤ) * n, z - δ - (v : ℤ) * n)
  let A := Finset.antidiagonal (factor β v hv : LaurentSeries ℚ).isPWO_support
    L.isPWO_support (z - δ)
  have hsub : A ⊆ S.image f := by
    intro ij hij
    obtain ⟨hi, hj, hij⟩ := Finset.mem_antidiagonal.mp hij
    obtain ⟨n, hn⟩ := laurent_factor_support β v hv ij.1 hi
    have hj' : ij.2 = z - δ - (v : ℤ) * n := by omega
    have hex : ∃ u ∈ (he ij.2).toFinset, w u ≠ 0 := by
      by_contra h
      push Not at h
      apply hj
      rw [← hIH]
      exact Finset.sum_eq_zero h
    obtain ⟨u, hu, _⟩ := hex
    have hu' := (he ij.2).mem_toFinset.mp hu
    have hnS : n ∈ S := by
      refine Finset.mem_image.mpr ⟨(n, u), hg.mem_toFinset.mpr ?_, rfl⟩
      change e u + δ + (v : ℤ) * n = z
      change e u = ij.2 at hu'
      omega
    exact Finset.mem_image.mpr ⟨n, hnS, Prod.ext hn.symm hj'.symm⟩
  have hsum := Finset.sum_subset hsub (f := fun ij : ℤ × ℤ =>
    (factor β v hv : LaurentSeries ℚ).coeff ij.1 * L.coeff ij.2) (by
      intro ij hij hnot
      obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp hij
      have hdeg : (f n).1 + (f n).2 = z - δ := by dsimp [f]; ring
      have hh : (factor β v hv : LaurentSeries ℚ).coeff (f n).1 = 0 ∨
          L.coeff (f n).2 = 0 := by
        simpa only [A, Finset.mem_antidiagonal, HahnSeries.mem_support, hdeg,
          and_true, not_and_or, not_not] using hnot
      exact mul_eq_zero.mpr hh)
  rw [HahnSeries.coeff_mul, hsum, Finset.sum_image (g := f)]
  · apply Finset.sum_congr rfl
    intro n _
    dsimp [f]
    rw [laurent_factor_coeff]
  · intro n _ m _ h
    have hh := congrArg Prod.fst h
    dsimp [f] at hh
    exact_mod_cast (mul_left_cancel₀ (Int.natCast_ne_zero.mpr hv) hh)

private theorem affine_fibre_laurent_coeff_int {K : Type*} (e : K → ℤ) (w : K → ℚ)
    (δ v : ℤ) (hv : 0 < v) (β c : ℚ) (z : ℤ)
    (hg : Set.Finite {u : ℕ × K | e u.2 + δ + v * u.1 = z})
    (he : ∀ k : ℤ, Set.Finite {u | e u = k}) (L : LaurentSeries ℚ)
    (hIH : ∀ k, (∑ u ∈ (he k).toFinset, w u) = L.coeff k) :
    c * (∑ n ∈ hg.toFinset.image Prod.fst,
      β ^ n * ∑ u ∈ (he (z - δ - v * n)).toFinset, w u) =
      (HahnSeries.single δ c * (factor β v.toNat (by omega) : LaurentSeries ℚ) * L).coeff z := by
  have hv' : (v.toNat : ℤ) = v := Int.toNat_of_nonneg (by omega)
  simpa only [hv'] using affine_fibre_laurent_coeff e w δ v.toNat (by omega) β c z
    (by simpa only [hv'] using hg) he L hIH

variable {I X : Type*} [AddCommGroup X]
section Family
variable {a b : List (Letter I)} {ε : Bool} {i : I}
variable {M N : Set (List (TMove (Letter I)))}
variable (hM : ∀ R ∈ M, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R ∧
  StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
variable (hN : ∀ S ∈ N, IsMatching₂ (a ++ b) [] S ∧ StrictReduced₂ (a ++ b) S)
variable (q : {R : List (TMove (Letter I)) | R ∈ M ∧
  Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)} → ℕ → ℕ × ℕ)
variable (r : N → ℕ → ℕ × ℕ)
variable (hq : ∀ R j, j ∈ leftEnds₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val →
  OnStrand₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val j (q R j))
variable (hr : ∀ S j, j ∈ leftEnds₂ (a ++ b) S.val → OnStrand₂ (a ++ b) S.val j (r S j))
variable (τ : ∀ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
    Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}),
    (MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ) → List (DTMove I))
variable (υ : ∀ S : N, (MatchingStrand (a ++ b) S.val → ℕ) → List (DTMove I))
variable (hτ : ∀ R c, Decorates₂ (a ++ (ε, i) :: (!ε, i) :: b) R.val (q R)
  (strandCounts c) (τ R c))
variable (hυ : ∀ S c, Decorates₂ (a ++ b) S.val (r S) (strandCounts c) (υ S c))

include hM hN hq hr hτ hυ

/-- Cap-class coefficients equal those of the shifted geometric dot factor
multiplied by `L`. The sole form-comparison premise `hIH` identifies the
shorter-word weighted fibers with `L.coeff` at every integer degree, as in
BE2 Theorem 10.3 Claim 5's induction hypothesis. All finiteness, grading and
cap enumeration come from the decorated-family correspondence. This theorem
is only the cap-class step, not the cancellation of the other classes. -/
theorem cap_labelled_family_laurent_coefficients
    (hMrep : ∀ R, IsMatching₂ (a ++ (ε, i) :: (!ε, i) :: b) [] R →
      StrictReduced₂ (a ++ (ε, i) :: (!ε, i) :: b) R →
      ∃ S ∈ M, Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S)
        (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R))
    (hNrep : ∀ R, IsMatching₂ (a ++ b) [] R → StrictReduced₂ (a ++ b) R →
      ∃ S ∈ N, Iso (pairing₂ (a ++ b) S) (pairing₂ (a ++ b) R))
    (hMuniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R)
        (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) S) → R = S)
    (hNuniq : ∀ R ∈ N, ∀ S ∈ N,
      Iso (pairing₂ (a ++ b) R) (pairing₂ (a ++ b) S) → R = S)
    (D : Datum I X) (sy : Symmetrizer D) (μ : X) :
    let J := Σ R : ({R : List (TMove (Letter I)) | R ∈ M ∧
      Same (pairing₂ (a ++ (ε, i) :: (!ε, i) :: b) R) b.length (b.length + 1)}),
      MatchingStrand (a ++ (ε, i) :: (!ε, i) :: b) R.val → ℕ
    let K := Σ S : N, MatchingStrand (a ++ b) S.val → ℕ
    let d := fun t : J => tableDegree D sy μ
      (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ t.1 t.2))
    let e := fun u : K => tableDegree D sy μ (dLay (a ++ b) (υ u.1 u.2))
    let p := fun t : J => xpar D μ (dLay (a ++ (ε, i) :: (!ε, i) :: b) (τ t.1 t.2))
    let p' := fun u : K => xpar D μ (dLay (a ++ b) (υ u.1 u.2))
    let δ := sy.d i * (1 + if !ε then D.h i (wt D μ b) else -D.h i (wt D μ b))
    ∃ (hf : ∀ z : ℤ, Set.Finite {t | d t = z})
      (he : ∀ z : ℤ, Set.Finite {u | e u = z}),
      ∀ (σ : ℚ), σ ^ 2 = 1 → ∀ (L : LaurentSeries ℚ),
        (∀ k, (∑ u ∈ (he k).toFinset, σ ^ (p' u).val) = L.coeff k) → ∀ z,
        (∑ t ∈ (hf z).toFinset, σ ^ (p t).val) =
          (HahnSeries.single δ (σ ^ (cupPar D (wt D μ b) (!ε, i)).val) *
            (factor (σ ^ (D.parity i).val) (2 * sy.d i).toNat
              (by have := sy.pos i; omega) :
              LaurentSeries ℚ) * L).coeff z := by
  obtain ⟨_, _, hF⟩ := cap_labelled_family_coefficients (X := X)
    hM hN q r hq hr τ υ hτ hυ hMrep hNrep hMuniq hNuniq
  dsimp only at hF ⊢
  obtain ⟨hf, hg, he, _, hc⟩ := hF D sy μ
  refine ⟨hf, he, ?_⟩
  intro σ hσ L hIH z
  refine (hc σ hσ z).2.trans ?_
  exact affine_fibre_laurent_coeff_int _ _ _ (2 * sy.d i)
    (by have := sy.pos i; omega) _ _ z (hg z) he L hIH

end Family
end OddMath.SKM

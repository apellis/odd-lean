/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import OddMath.SKM.MixedFibres
import OddMath.CoveringQuantum.CapScalar

/-! # Graphical generating expression for BE2 Theorem 10.3

The infinite decorated sum is represented by a finite sum of undecorated
monomials times the strand normalization inverses. Its coefficients are computed
from the generator table for independently chosen valid serializers. No algebraic
form, coverage, reducedness, finite colour type, or bar consistency is assumed.
-/
noncomputable section
namespace OddMath.SKM.GraphicalSeries
open StringDiagrams StringDiagrams.Chord CoveringQuantum CoveringQuantum.UDot
open CoveringQuantum.PreF.DotSeries
open scoped BigOperators LaurentSeries

private theorem count_fiber_finite {ι : Type*} [Fintype ι] (w : ι → ℕ)
    (hw : ∀ i, w i ≠ 0) (m : ℕ) :
    Set.Finite {c : ι → ℕ | ∑ i, w i * c i = m} := by
  classical
  have h := Set.Finite.preimage (countEnergy_injective w hw).injOn
    (Finset.finsuppAntidiag (Finset.univ : Finset ι) m).finite_toSet
  convert h using 1
  ext c
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Finset.mem_coe, countEnergy_mem]

private theorem coeff_strands_counts {ι k : Type*} [Fintype ι] [CommRing k]
    (a : ι → k) (w : ι → ℕ) (hw : ∀ i, w i ≠ 0) (m : ℕ)
    (hf : Set.Finite {c : ι → ℕ | ∑ i, w i * c i = m}) :
    (∑ c ∈ hf.toFinset, ∏ i, a i ^ c i) =
      PowerSeries.coeff m (strands a w hw) := by
  classical
  rw [coeff_strands]
  have hs (c : ι → ℕ) :
      (∏ i, if w i ∣ countEnergy w c i then a i ^ (countEnergy w c i / w i) else 0) =
        ∏ i, a i ^ c i := by
    simp [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (hw _))]
  refine Finset.sum_bij_ne_zero (fun c _ _ => countEnergy w c) ?_ ?_ ?_ ?_
  · intro c hc _
    exact (countEnergy_mem w c m).2 (hf.mem_toFinset.mp hc)
  · intro c _ _ d _ _ h
    exact countEnergy_injective w hw h
  · intro l hl hn
    have hd : ∀ i, w i ∣ l i := by
      intro i
      by_contra hi
      apply hn
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
    obtain ⟨c, rfl⟩ := (exists_countEnergy_iff w l).2 hd
    refine ⟨c, hf.mem_toFinset.mpr ((countEnergy_mem w c m).1 hl), ?_, rfl⟩
    simpa only [hs] using hn
  · intro c _ _
    exact (hs c).symm

private theorem parity_pow_add {k : Type*} [CommRing k] (π : k) (hπ : π ^ 2 = 1)
    (u v : ZMod 2) : π ^ (u + v).val = π ^ u.val * π ^ v.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hπ, pow_add]

private theorem parity_pow_count {k : Type*} [CommRing k] (π : k) (hπ : π ^ 2 = 1)
    (v : ZMod 2) (c : ℕ) : π ^ ((c : ZMod 2) * v).val = (π ^ v.val) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.cast_succ, add_mul, one_mul, parity_pow_add π hπ, ih, pow_succ]

private theorem parity_pow_sum {ι k : Type*} [Fintype ι] [CommRing k]
    (π : k) (hπ : π ^ 2 = 1) (v : ι → ZMod 2) (c : ι → ℕ) :
    π ^ (∑ i, (c i : ZMod 2) * v i).val = ∏ i, (π ^ (v i).val) ^ c i := by
  classical
  have hs (s : Finset ι) : π ^ (∑ i ∈ s, (c i : ZMod 2) * v i).val =
      ∏ i ∈ s, (π ^ (v i).val) ^ c i := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, parity_pow_add π hπ,
        parity_pow_count π hπ, ih]
  exact hs Finset.univ

private theorem shifted_counts_coeff {I J k : Type*} [Fintype J] [CommRing k]
    (C : CoveringQuantum.SuperCartanDatum I) (π : k) (hπ : π ^ 2 = 1)
    (b : J → I) (κ z : ℤ) (ε : ZMod 2) :
    ∃ hf : Set.Finite {c : J → ℕ | κ + ((∑ t, 2 * C.d (b t) * c t : ℕ) : ℤ) = z},
      (∑ c ∈ hf.toFinset, π ^ (ε + ∑ t, (c t : ZMod 2) * C.parity (b t)).val) =
        if κ ≤ z then π ^ ε.val * PowerSeries.coeff (z - κ).toNat
          (strands (fun t => C.pii π (b t)) (fun t => 2 * C.d (b t))
            (fun t => Nat.ne_of_gt (by have := C.d_pos (b t); omega)))
        else 0 := by
  classical
  let w : J → ℕ := fun t => 2 * C.d (b t)
  have hw : ∀ t, w t ≠ 0 := fun t => Nat.ne_of_gt (by
    have := C.d_pos (b t)
    dsimp [w]
    omega)
  by_cases hz : κ ≤ z
  · have hm : ((z - κ).toNat : ℤ) = z - κ := Int.toNat_of_nonneg (sub_nonneg.mpr hz)
    have heq : {c : J → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} =
        {c : J → ℕ | ∑ t, w t * c t = (z - κ).toNat} := by
      ext c
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hc
        exact_mod_cast (show ((∑ t, w t * c t : ℕ) : ℤ) = ((z - κ).toNat : ℤ) by omega)
      · intro hc
        rw [hc, hm]
        omega
    have hf := count_fiber_finite w hw (z - κ).toNat
    have hf' : Set.Finite {c : J → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} :=
      heq ▸ hf
    refine ⟨hf', ?_⟩
    rw [ite_eq_left hz]
    have ht : hf'.toFinset = hf.toFinset := by ext c; simp only [Set.Finite.mem_toFinset, heq]
    rw [ht]
    simp_rw [parity_pow_add π hπ, parity_pow_sum π hπ]
    rw [← Finset.mul_sum]
    congr 1
    exact coeff_strands_counts (fun t => C.pii π (b t)) w hw (z - κ).toNat hf
  · have heq : {c : J → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hn : (0 : ℤ) ≤ ((∑ t, w t * c t : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
    have hf : Set.Finite {c : J → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} :=
      heq ▸ Set.finite_empty
    refine ⟨hf, ?_⟩
    have ht : hf.toFinset = ∅ := by
      ext c
      simp only [Set.Finite.mem_toFinset, heq, Set.mem_empty_iff_false, Finset.notMem_empty]
    rw [ht, Finset.sum_empty, ite_eq_right hz]


variable {I X : Type*} [AddCommGroup X]

/-- One undecorated matching and its independent strand normalization factors. -/
def term (D : RootDatum I X) (μ : X) (a : List (Letter I))
    (R : List (TMove (Letter I))) : Coefficients.Ring :=
  qp Coefficients.q (tableDegree D.toSKM D.skmSymmetrizer μ (tLay a R)) *
    Coefficients.pi ^ (xpar D.toSKM μ (tLay a R)).val *
      ∏ j : MatchingStrand a R, D.norm Coefficients.q Coefficients.pi
        (matchingStrandColour a R j)

/-- The finite covering-ring interpretation of the graphical decorated sum.
Finiteness follows from uniqueness of the endpoint pairings. -/
def expression (D : RootDatum I X) (μ : X) (a b : List (Letter I))
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S) :
    Coefficients.Ring :=
  letI := (matching_representatives_finite a b M hM huniq).fintype
  ∑ R : M, term D μ a R.val

private theorem shifted_series_coeff (f : PowerSeries ℚ) (k z : ℤ) (c : ℚ) :
    ((HahnSeries.single k c : LaurentSeries ℚ) * (f : LaurentSeries ℚ)).coeff z =
      if k ≤ z then c * PowerSeries.coeff (z - k).toNat f else 0 := by
  rw [HahnSeries.coeff_single_mul, PowerSeries.coeff_coe]
  by_cases h : k ≤ z
  · rw [ite_eq_right (by omega), ite_eq_left h]
    have he : (z - k).natAbs = (z - k).toNat := by omega
    rw [he]
  · rw [ite_eq_left (by omega), ite_eq_right h, mul_zero]

/-- Laurent expansion of one summand, independent of all dot placement choices. -/
theorem signLaurent_term (D : RootDatum I X) (μ : X) (a : List (Letter I))
    (R : List (TMove (Letter I))) (σ : ℚ) (hσ : σ ^ 2 = 1) :
    signLaurent σ hσ (term D μ a R) =
      HahnSeries.single (tableDegree D.toSKM D.skmSymmetrizer μ (tLay a R))
        (σ ^ (xpar D.toSKM μ (tLay a R)).val) *
      (strands (fun j : MatchingStrand a R => D.pii σ (matchingStrandColour a R j))
        (fun j => 2 * D.d (matchingStrandColour a R j))
        (fun j => Nat.ne_of_gt (by have := D.d_pos (matchingStrandColour a R j); omega)) :
        LaurentSeries ℚ) := by
  classical
  simp only [term, map_mul, map_pow, signLaurent_qp, signLaurent_pi, map_prod,
    CapScalar.signLaurent_norm, strands]
  rw [← map_pow]
  change (HahnSeries.single _ 1 * HahnSeries.single 0 _) * _ = _
  rw [HahnSeries.single_mul_single, add_zero, one_mul]

private theorem term_coeff (D : RootDatum I X) (μ : X)
    {a b : List (Letter I)} {R : List (TMove (Letter I))}
    (hR : IsMatching₂ a b R) (q : ℕ → ℕ × ℕ)
    (hq : ∀ j ∈ leftEnds₂ a R, OnStrand₂ a R j (q j))
    (τ : (MatchingStrand a R → ℕ) → List (DTMove I))
    (hτ : ∀ c, Decorates₂ a R q (strandCounts c) (τ c))
    (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ)
    (hf : Set.Finite {c : MatchingStrand a R → ℕ |
      tableDegree D.toSKM D.skmSymmetrizer μ (dLay a (τ c)) = z}) :
    (signLaurent σ hσ (term D μ a R)).coeff z =
      ∑ c ∈ hf.toFinset, σ ^ (xpar D.toSKM μ (dLay a (τ c))).val := by
  classical
  rw [signLaurent_term, shifted_series_coeff]
  obtain ⟨hg, he⟩ := shifted_counts_coeff D.toSuperCartanDatum σ hσ
    (matchingStrandColour a R)
    (tableDegree D.toSKM D.skmSymmetrizer μ (tLay a R)) z
    (xpar D.toSKM μ (tLay a R))
  rw [← he]
  have hd (c : MatchingStrand a R → ℕ) :
      tableDegree D.toSKM D.skmSymmetrizer μ (dLay a (τ c)) =
        tableDegree D.toSKM D.skmSymmetrizer μ (tLay a R) +
          ((∑ j, 2 * D.d (matchingStrandColour a R j) * c j : ℕ) : ℤ) := by
    rw [(mixed_decorated_degree_parity D.toSKM D.skmSymmetrizer μ hR q hq c _ (hτ c)).1]
    simp only [RootDatum.skmSymmetrizer_d, Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : hg.toFinset = hf.toFinset := by
    ext c
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, hd]
  rw [hs]
  apply Finset.sum_congr rfl
  intro c _
  rw [(mixed_decorated_degree_parity D.toSKM D.skmSymmetrizer μ hR q hq c _ (hτ c)).2]
  rfl

/-- Every Laurent coefficient of the finite graphical expression is the weighted
sum over the entire degree fibre of any independently chosen valid serializers.
Both finiteness statements are proved from matching uniqueness and positive dot
degrees; there is no cutoff or degree-bound hypothesis. -/
theorem expression_coeff (D : RootDatum I X) (μ : X)
    (a b : List (Letter I)) (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ a b R)
    (huniq : ∀ R ∈ M, ∀ S ∈ M, Iso (pairing₂ a R) (pairing₂ a S) → R = S)
    (q : M → ℕ → ℕ × ℕ)
    (hq : ∀ R j, j ∈ leftEnds₂ a R.val → OnStrand₂ a R.val j (q R j))
    (τ : ∀ R : M, (MatchingStrand a R.val → ℕ) → List (DTMove I))
    (hτ : ∀ R c, Decorates₂ a R.val (q R) (strandCounts c) (τ R c))
    (σ : ℚ) (hσ : σ ^ 2 = 1) (z : ℤ) :
    (signLaurent σ hσ (expression D μ a b M hM huniq)).coeff z =
      ∑ t ∈ (mixed_labelled_degree_finite D.toSKM D.skmSymmetrizer μ a b M
        hM huniq q hq τ hτ z).toFinset,
        σ ^ (xpar D.toSKM μ (dLay a (τ t.1 t.2))).val := by
  classical
  let _ := (matching_representatives_finite a b M hM huniq).fintype
  let hf := mixed_labelled_degree_finite D.toSKM D.skmSymmetrizer μ a b M
    hM huniq q hq τ hτ z
  have hg (R : M) : Set.Finite {c : MatchingStrand a R.val → ℕ |
      tableDegree D.toSKM D.skmSymmetrizer μ (dLay a (τ R c)) = z} := by
    exact hf.preimage sigma_mk_injective.injOn
  change (signLaurent σ hσ (∑ R : M, term D μ a R.val)).coeff z = _
  rw [map_sum, HahnSeries.coeff_sum]
  simp_rw [term_coeff D μ (hM _ (Subtype.property _)) _ (hq _) _ (hτ _) σ hσ z (hg _)]
  rw [Finset.sum_sigma']
  have hs : Finset.univ.sigma (fun R : M => (hg R).toFinset) = hf.toFinset := by
    ext t
    simp only [Finset.mem_sigma, Finset.mem_univ, true_and, Set.Finite.mem_toFinset,
      Set.mem_ofPred_eq]
  rw [hs]

end OddMath.SKM.GraphicalSeries

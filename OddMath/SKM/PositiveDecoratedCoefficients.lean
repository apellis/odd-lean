/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PositiveDecoratedGrading
import OddMath.SKM.CoveringDatum
import OddMath.CoveringQuantum.PreF.DotSeries

/-!
# Integer-degree coefficients for a positive decorated matching

The contribution of one positive strictly reduced matching in [BE2,
arXiv:1701.04133v2, proof of Theorem 10.3, Claim 1] is a crossing shift of the
formal dot series. `positive_decorated_coeff` constructs ordinary diagrams at one
valid top placement, proves that every integer-degree fiber is finite, and computes
its parity-weighted sum. The crossing shift may be negative; degrees below it give
zero rather than the constant coefficient obtained by truncating a negative integer.

The finite reindexing uses `DotSeries.countEnergy`, with one count per target
strand. Its zero-summand argument does not assume the coefficient ring is a domain.
Parity exponents are reduced modulo two using only `π ^ 2 = 1`.

This is a single-representative contribution, not full Claim 1. Summing over
matching representatives, independence of representatives and distinguished points,
and comparison with the algebraic form remain open. In particular this does not
remove the algebraic form's finite-colour or `BarConsistent` restrictions, and does
not specialize the whole rational-function coefficient field.
-/

noncomputable section
open scoped BigOperators
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open CoveringQuantum.PreF.DotSeries

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

private theorem shifted_counts_coeff {I k : Type*} [CommRing k]
    (C : CoveringQuantum.SuperCartanDatum I) (π : k) (hπ : π ^ 2 = 1)
    {n : ℕ} (b : Fin n → I) (κ z : ℤ) (ε : ZMod 2) :
    ∃ hf : Set.Finite {c : Fin n → ℕ | κ + ((∑ t, 2 * C.d (b t) * c t : ℕ) : ℤ) = z},
      (∑ c ∈ hf.toFinset, π ^ (ε + ∑ t, (c t : ZMod 2) * C.parity (b t)).val) =
        if κ ≤ z then π ^ ε.val * PowerSeries.coeff (z - κ).toNat (C.dotSeries π b)
        else 0 := by
  classical
  let w : Fin n → ℕ := fun t => 2 * C.d (b t)
  have hw : ∀ t, w t ≠ 0 := fun t => Nat.ne_of_gt (by
    have := C.d_pos (b t)
    dsimp [w]
    omega)
  by_cases hz : κ ≤ z
  · have hm : ((z - κ).toNat : ℤ) = z - κ := Int.toNat_of_nonneg (sub_nonneg.mpr hz)
    have heq : {c : Fin n → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} =
        {c : Fin n → ℕ | ∑ t, w t * c t = (z - κ).toNat} := by
      ext c
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hc
        exact_mod_cast (show ((∑ t, w t * c t : ℕ) : ℤ) = ((z - κ).toNat : ℤ) by omega)
      · intro hc
        rw [hc, hm]
        omega
    have hf := count_fiber_finite w hw (z - κ).toNat
    have hf' : Set.Finite {c : Fin n → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} :=
      heq ▸ hf
    refine ⟨hf', ?_⟩
    rw [ite_eq_left hz]
    have ht : hf'.toFinset = hf.toFinset := by ext c; simp only [Set.Finite.mem_toFinset, heq]
    rw [ht]
    simp_rw [parity_pow_add π hπ, parity_pow_sum π hπ]
    rw [← Finset.mul_sum]
    congr 1
    exact coeff_strands_counts (fun t => C.pii π (b t)) w hw (z - κ).toNat hf
  · have heq : {c : Fin n → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} = ∅ := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      have hn : (0 : ℤ) ≤ ((∑ t, w t * c t : ℕ) : ℤ) := Int.natCast_nonneg _
      omega
    have hf : Set.Finite {c : Fin n → ℕ | κ + ((∑ t, w t * c t : ℕ) : ℤ) = z} :=
      heq ▸ Set.finite_empty
    refine ⟨hf, ?_⟩
    have ht : hf.toFinset = ∅ := by
      ext c
      simp only [Set.Finite.mem_toFinset, heq, Set.mem_empty_iff_false, Finset.notMem_empty]
    rw [ht, Finset.sum_empty, ite_eq_right hz]

/-- The coefficient contribution of one positive strictly reduced matching in
[BE2, arXiv:1701.04133v2, proof of Theorem 10.3, Claim 1]. A single valid top
placement is chosen before all dot counts. The fibers use the ordinary diagram
degree and their weights use its extended-layer parity. This is not the sum over
all representatives, nor the comparison with the algebraic form. -/
theorem positive_decorated_coeff {I X k : Type*} [AddCommGroup X] [CommRing k]
    (Q : CoveringQuantum.RootDatum I X) (μ : X) (π : k) (hπ : π ^ 2 = 1)
    {n : ℕ} (a b : Fin n → I)
    {R : List (TMove (Letter I))}
    (hR : IsMatching₂ (List.ofFn fun r => (true, a r))
      (List.ofFn fun r => (true, b r)) R)
    (hred : StrictReduced₂ (List.ofFn fun r => (true, a r)) R)
    (e : Equiv.Perm (Fin n))
    (he : ∀ r, Same (pairing₂ (List.ofFn fun r => (true, a r)) R)
      (n - 1 - r.val) (n + (e r).val)) :
    let C := Q.toSuperCartanDatum
    let κ : ℤ := ∑ r, ∑ s with r < s ∧ e s < e r,
      -C.dot (a r) (a s)
    let ε : ZMod 2 := ∑ r, ∑ s with r < s ∧ e s < e r,
      Q.parity (a r) * Q.parity (a s)
    ∃ p : MatchingStrand (List.ofFn fun r => (true, a r)) R ≃ Fin n,
      (∀ j : MatchingStrand (List.ofFn fun r => (true, a r)) R,
        OnStrand₂ (List.ofFn fun r => (true, a r)) R j.val (R.length, (p j).val)) ∧
      ∃ (L : (Fin n → ℕ) → List (LayerData I))
        (hL : ∀ c, SChain (List.ofFn fun r => (true, a r)) (L c) (List.ofFn fun r => (true, b r))),
        (∀ c, (L c).map ofL = dLay (List.ofFn fun r => (true, a r))
          (topDotMoves (List.ofFn fun r => (true, a r)) R (fun j => (p j).val) (fun j => c (p j)))) ∧
        (let deg : (Fin n → ℕ) → ℤ := fun c =>
           Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
             (mkD Q.toSKM μ (L c) (hL c))
         let par : (Fin n → ℕ) → ZMod 2 := fun c =>
           xpar Q.toSKM μ ((L c).map ofL)
         ∀ z : ℤ, ∃ hf : Set.Finite {c : Fin n → ℕ | deg c = z},
           (∑ c ∈ hf.toFinset, π ^ (par c).val) =
             if κ ≤ z then
               π ^ ε.val * PowerSeries.coeff (z - κ).toNat (C.dotSeries π b)
             else 0) := by
  classical
  dsimp only
  obtain ⟨p, hp, hg⟩ := positive_decorated_degree_parity
    Q.toSKM Q.skmSymmetrizer μ a b hR hred e he
  choose L hL hmap hdeg hpar using hg
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  have hd (c : Fin n → ℕ) :
      Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer) (mkD Q.toSKM μ (L c) (hL c)) =
        (∑ r, ∑ s with r < s ∧ e s < e r, -Q.toSuperCartanDatum.dot (a r) (a s)) +
        ((∑ t, 2 * Q.d (b t) * c t : ℕ) : ℤ) := by
    rw [hdeg c]
    simp only [CoveringQuantum.RootDatum.skm_crossing_weight]
    simp only [CoveringQuantum.RootDatum.skmSymmetrizer_d,
      Nat.cast_sum, Nat.cast_mul, Nat.cast_ofNat]
    congr 1
    apply Finset.sum_congr rfl
    intro t _
    ring
  have hpa (c : Fin n → ℕ) : xpar Q.toSKM μ ((L c).map ofL) =
      (∑ r, ∑ s with r < s ∧ e s < e r, Q.parity (a r) * Q.parity (a s)) +
        ∑ t, (c t : ZMod 2) * Q.parity (b t) := by
    rw [hmap c]
    exact hpar c
  simp only [hd, hpa]
  intro z
  exact shifted_counts_coeff Q.toSuperCartanDatum π hπ b _ z _

end OddMath.SKM

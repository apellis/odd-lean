import OddMath.SKM.LeftDot

/-! Actual paired-sector components of the full mixed inversion matrix.
The low-dot pivots are units, so no exterior coefficient is cancelled. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

theorem cpow_uL_eL (i : I) (μ : X) (b s : ℕ) :
    cpow (uLM D Sc i μ) b ≫ eLM D Sc i μ s = eLM D Sc i μ (b + s) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [cpow_succ', Category.assoc, ih, uL_eL]
    congr 1
    omega

theorem hL_cpow_uR (i : I) (μ : X) (s b : ℕ) :
    hLM D Sc i μ s ≫ cpow (uRM D Sc i μ) b = hLM D Sc i μ (s + b) := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [cpow_succ, ← Category.assoc, ih, hL_uR]
    congr 1

theorem paired_target_low (cs : CScalars Sc) (i : I) (μ : X) (b s : ℕ)
    (hlt : ((b + s : ℕ) : ℤ) < D.h i μ) :
    etaP cs i μ ≫ cpow (uLM D Sc i μ) b ≫ eLM D Sc i μ s =
      if ((b + s : ℕ) : ℤ) = D.h i μ - 1
      then (cs.c μ i : k) • 𝟙 _ else 0 := by
  rw [cpow_uL_eL]
  exact etaP_eL_lt cs i μ (b + s) hlt

theorem paired_source_low (cs : CScalars Sc) (i : I) (μ : X) (s b : ℕ)
    (hlt : ((s + b : ℕ) : ℤ) < -D.h i μ) :
    hLM D Sc i μ s ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ =
      if ((s + b : ℕ) : ℤ) = -D.h i μ - 1
      then (↑(cs.c μ i)⁻¹ : k) • 𝟙 _ else 0 := by
  rw [← Category.assoc, hL_cpow_uR]
  exact hL_epsP_lt cs i μ (s + b) hlt

/-- One actual target-side paired row under the principal crossing. -/
theorem paired_target_step (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    etaP cs i μ ≫ cpow (uLM D Sc i μ) (b + 1) ≫ sgM D Sc i μ =
      zsign k (D.parity i) •
        (etaP cs i μ ≫ cpow (uLM D Sc i μ) b ≫ sgM D Sc i μ ≫ uRM D Sc i μ -
         etaP cs i μ ≫ eLM D Sc i μ b ≫ hLM D Sc i μ 0) := by
  rw [cpow_succ, Category.assoc, uL_sg, Linear.comp_smul,
    Preadditive.comp_sub, Linear.comp_smul, Preadditive.comp_sub]
  have he : cpow (uLM D Sc i μ) b ≫ eLM D Sc i μ 0 ≫ hLM D Sc i μ 0 =
      eLM D Sc i μ b ≫ hLM D Sc i μ 0 := by
    rw [← Category.assoc, cpow_uL_eL, Nat.add_zero]
  rw [he]

/-- The source-side paired recurrence uses the same right adjunction. -/
theorem paired_source_step (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    sgM D Sc i μ ≫ cpow (uRM D Sc i μ) (b + 1) ≫ epsP cs i μ =
      zsign k (D.parity i) •
        (uLM D Sc i μ ≫ sgM D Sc i μ ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ) +
      eLM D Sc i μ 0 ≫ hLM D Sc i μ b ≫ epsP cs i μ := by
  have hs := sg_uR (Sc := Sc) i μ
  rw [sub_eq_iff_eq_add] at hs
  rw [cpow_succ']
  simp only [← Category.assoc]
  rw [hs]
  simp only [Preadditive.add_comp, Linear.smul_comp, Category.assoc]
  have he : hLM D Sc i μ 0 ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ =
      hLM D Sc i μ b ≫ epsP cs i μ := by
    rw [← Category.assoc, hL_cpow_uR, Nat.zero_add]
  rw [he]
  abel

/-- The nonpositive-height initial target row has one unit leading cup;
every inverse-block correction has a strictly smaller cup index. -/
theorem paired_target_initial (cs : CScalars Sc) (i : I) (μ : X)
    (hh : D.h i μ ≤ 0) :
    etaP cs i μ ≫ sgM D Sc i μ =
      (zsign k (ipar D i μ) * (cs.c μ i : k)) •
        ((∑ j ∈ Finset.range (-D.h i μ).toNat,
          hLM D Sc i μ (-D.h i μ).toNat ≫ dkM D Sc i μ j ≫ hLM D Sc i μ j) -
          hLM D Sc i μ (-D.h i μ).toNat) := by
  rw [etaP_of_nonpos cs i μ hh, Linear.smul_comp, Category.assoc,
    lc_sg_nonpos i μ hh, Preadditive.comp_sub, Preadditive.comp_sum,
    Category.comp_id]

/-- The dual initial source row has a unit leading cap and only
strictly smaller cap indices in its inverse-block corrections. -/
theorem paired_source_initial (cs : CScalars Sc) (i : I) (μ : X)
    (hh : 0 ≤ D.h i μ) :
    sgM D Sc i μ ≫ epsP cs i μ =
      (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))) •
        ((∑ j ∈ Finset.range (D.h i μ).toNat,
          eLM D Sc i μ j ≫ dcM D Sc i μ j ≫ eLM D Sc i μ (D.h i μ).toNat) -
          eLM D Sc i μ (D.h i μ).toNat) := by
  rw [epsP_of_nonneg cs i μ hh, Linear.comp_smul, ← Category.assoc,
    sg_lc, Preadditive.sub_comp, Preadditive.sum_comp, Category.id_comp]
  simp only [Category.assoc]

/-- Finite all-weight target expansion. Only the isolated cup index
changes; all closed coefficients stay on its residual side. -/
theorem paired_target_expansion (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    etaP cs i μ ≫ cpow (uLM D Sc i μ) b ≫ sgM D Sc i μ =
      (zsign k (D.parity i)) ^ b •
        (etaP cs i μ ≫ sgM D Sc i μ ≫ cpow (uRM D Sc i μ) b) +
      ∑ s ∈ Finset.range b, (-((zsign k (D.parity i)) ^ (s + 1))) •
        (etaP cs i μ ≫ eLM D Sc i μ (b - 1 - s) ≫ hLM D Sc i μ s) := by
  have h := iter_slide (uLM D Sc i μ) (uRM D Sc i μ) (sgM D Sc i μ)
    (-(zsign k (D.parity i)) • (eLM D Sc i μ 0 ≫ hLM D Sc i μ 0))
    (zsign k (D.parity i))
    (by rw [uL_sg, smul_sub, neg_smul]; rfl) b
  rw [h, Preadditive.comp_add, Linear.comp_smul, Preadditive.comp_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  simp only [Linear.comp_smul, Linear.smul_comp, smul_smul]
  have he : cpow (uLM D Sc i μ) (b - 1 - s) ≫ eLM D Sc i μ 0 =
      eLM D Sc i μ (b - 1 - s) := by rw [cpow_uL_eL, Nat.add_zero]
  have hh : hLM D Sc i μ 0 ≫ cpow (uRM D Sc i μ) s = hLM D Sc i μ s := by
    rw [hL_cpow_uR, Nat.zero_add]
  simp only [← Category.assoc, he]
  simp only [Category.assoc, hh]
  rw [mul_neg, ← pow_succ]

/-- Finite all-weight source expansion with residual loops to the right
of the isolated cap, before any coefficient placement or parity transport. -/
theorem paired_source_expansion (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    sgM D Sc i μ ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ =
      (zsign k (D.parity i)) ^ b •
        (cpow (uLM D Sc i μ) b ≫ sgM D Sc i μ ≫ epsP cs i μ) +
      ∑ s ∈ Finset.range b, (zsign k (D.parity i)) ^ s •
        (eLM D Sc i μ s ≫ hLM D Sc i μ (b - 1 - s) ≫ epsP cs i μ) := by
  have hs := sg_uR (Sc := Sc) i μ
  rw [sub_eq_iff_eq_add] at hs
  have h := iter_slide' (uLM D Sc i μ) (uRM D Sc i μ) (sgM D Sc i μ)
    (eLM D Sc i μ 0 ≫ hLM D Sc i μ 0) (zsign k (D.parity i))
    (by simpa only [add_comm] using hs) b
  rw [← Category.assoc, h, Preadditive.add_comp, Linear.smul_comp,
    Preadditive.sum_comp]
  simp only [Category.assoc]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  rw [Linear.smul_comp]
  have he : cpow (uLM D Sc i μ) s ≫ eLM D Sc i μ 0 = eLM D Sc i μ s := by
    rw [cpow_uL_eL, Nat.add_zero]
  have hh : hLM D Sc i μ 0 ≫ cpow (uRM D Sc i μ) (b - 1 - s) =
      hLM D Sc i μ (b - 1 - s) := by rw [hL_cpow_uR, Nat.zero_add]
  simp only [← Category.assoc, he]
  simp only [Category.assoc, hh]

/-- At positive height the target paired row has the indicated unit pivot;
the displayed sum involves only strictly smaller isolated cup indices. -/
theorem paired_target_leading_pos (cs : CScalars Sc) (i : I) (μ : X) (N m : ℕ)
    (hN : D.h i μ = (N : ℤ)) (hpos : 0 < N) :
    etaP cs i μ ≫ cpow (uLM D Sc i μ) (N + m) ≫ sgM D Sc i μ =
      (-((zsign k (D.parity i)) ^ (m + 1)) * (cs.c μ i : k)) • hLM D Sc i μ m +
      ∑ s ∈ Finset.range m, (-((zsign k (D.parity i)) ^ (s + 1))) •
        (etaP cs i μ ≫ eLM D Sc i μ (N + m - 1 - s) ≫ hLM D Sc i μ s) := by
  rw [paired_target_expansion]
  rw [← Category.assoc, etaP_sg_pos cs i μ (by omega), Limits.zero_comp,
    smul_zero, zero_add]
  let f := fun s => (-((zsign k (D.parity i)) ^ (s + 1))) •
    (etaP cs i μ ≫ eLM D Sc i μ (N + m - 1 - s) ≫ hLM D Sc i μ s)
  have htrunc : (∑ s ∈ Finset.range (N + m), f s) =
      ∑ s ∈ Finset.range (m + 1), f s := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro s hs hn
    have hs' := Finset.mem_range.mp hs
    have hn' : m + 1 ≤ s := by simpa using hn
    dsimp [f]
    rw [← Category.assoc, etaP_eL_lt cs i μ (N + m - 1 - s) (by omega),
      ite_eq_right (by omega), Limits.zero_comp, smul_zero]
  change (∑ s ∈ Finset.range (N + m), f s) = _
  rw [htrunc, Finset.sum_range_succ]
  have hp : f m = (-((zsign k (D.parity i)) ^ (m + 1)) * (cs.c μ i : k)) •
      hLM D Sc i μ m := by
    dsimp [f]
    rw [← Category.assoc, etaP_eL_lt cs i μ (N + m - 1 - m) (by omega),
      ite_eq_left (by omega), Linear.smul_comp, Category.id_comp, smul_smul]
  rw [hp, add_comm]

/-- The negative-height source pivot is dual to the positive-height target
pivot and again uses only a scalar unit. -/
theorem paired_source_leading_neg (cs : CScalars Sc) (i : I) (μ : X) (N m : ℕ)
    (hN : -D.h i μ = (N : ℤ)) (hpos : 0 < N) :
    sgM D Sc i μ ≫ cpow (uRM D Sc i μ) (N + m) ≫ epsP cs i μ =
      ((zsign k (D.parity i)) ^ m * (↑(cs.c μ i)⁻¹ : k)) • eLM D Sc i μ m +
      ∑ s ∈ Finset.range m, (zsign k (D.parity i)) ^ s •
        (eLM D Sc i μ s ≫ hLM D Sc i μ (N + m - 1 - s) ≫ epsP cs i μ) := by
  rw [paired_source_expansion, eq_2_14_a cs i μ (by omega),
    Limits.comp_zero, smul_zero, zero_add]
  let f := fun s => (zsign k (D.parity i)) ^ s •
    (eLM D Sc i μ s ≫ hLM D Sc i μ (N + m - 1 - s) ≫ epsP cs i μ)
  have htrunc : (∑ s ∈ Finset.range (N + m), f s) =
      ∑ s ∈ Finset.range (m + 1), f s := by
    symm
    apply Finset.sum_subset (Finset.range_mono (by omega))
    intro s hs hn
    have hs' := Finset.mem_range.mp hs
    have hn' : m + 1 ≤ s := by simpa using hn
    dsimp [f]
    rw [hL_epsP_lt cs i μ (N + m - 1 - s) (by omega),
      ite_eq_right (by omega), Limits.comp_zero, smul_zero]
  change (∑ s ∈ Finset.range (N + m), f s) = _
  rw [htrunc, Finset.sum_range_succ]
  have hp : f m = ((zsign k (D.parity i)) ^ m * (↑(cs.c μ i)⁻¹ : k)) •
      eLM D Sc i μ m := by
    dsimp [f]
    rw [hL_epsP_lt cs i μ (N + m - 1 - m) (by omega),
      ite_eq_left (by omega), Linear.comp_smul, Category.comp_id, smul_smul]
  rw [hp, add_comm]

/-- The nonpositive target branch has two finite lower-index families:
the inverse-block corrections and the dot-slide corrections. -/
theorem paired_target_leading_nonpos (cs : CScalars Sc) (i : I) (μ : X) (N b : ℕ)
    (hN : -D.h i μ = (N : ℤ)) :
    etaP cs i μ ≫ cpow (uLM D Sc i μ) b ≫ sgM D Sc i μ =
      (-((zsign k (D.parity i)) ^ b *
        (zsign k (ipar D i μ) * (cs.c μ i : k)))) • hLM D Sc i μ (N + b) +
      (∑ j ∈ Finset.range N,
        ((zsign k (D.parity i)) ^ b * (zsign k (ipar D i μ) * (cs.c μ i : k))) •
          (hLM D Sc i μ N ≫ dkM D Sc i μ j ≫ hLM D Sc i μ (j + b))) +
      ∑ s ∈ Finset.range b, (-((zsign k (D.parity i)) ^ (s + 1))) •
        (etaP cs i μ ≫ eLM D Sc i μ (b - 1 - s) ≫ hLM D Sc i μ s) := by
  have hn : (-D.h i μ).toNat = N := by omega
  rw [paired_target_expansion, ← Category.assoc,
    paired_target_initial cs i μ (by omega), hn]
  simp only [Linear.smul_comp, Preadditive.sub_comp, Preadditive.sum_comp,
    Category.assoc, hL_cpow_uR, smul_sub, Finset.smul_sum, smul_smul, neg_smul]
  abel

/-- The nonnegative source branch has the corresponding leading cap;
all remaining isolated cap indices are strictly smaller. -/
theorem paired_source_leading_nonneg (cs : CScalars Sc) (i : I) (μ : X) (N b : ℕ)
    (hN : D.h i μ = (N : ℤ)) :
    sgM D Sc i μ ≫ cpow (uRM D Sc i μ) b ≫ epsP cs i μ =
      (-((zsign k (D.parity i)) ^ b *
        (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))))) •
          eLM D Sc i μ (b + N) +
      (∑ j ∈ Finset.range N,
        ((zsign k (D.parity i)) ^ b *
          (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k)))) •
          (eLM D Sc i μ (b + j) ≫ dcM D Sc i μ j ≫ eLM D Sc i μ N)) +
      ∑ s ∈ Finset.range b, (zsign k (D.parity i)) ^ s •
        (eLM D Sc i μ s ≫ hLM D Sc i μ (b - 1 - s) ≫ epsP cs i μ) := by
  have hn : (D.h i μ).toNat = N := by omega
  rw [paired_source_expansion, paired_source_initial cs i μ (by omega), hn]
  rw [Linear.comp_smul, smul_smul]
  simp only [Preadditive.comp_sub, Preadditive.comp_sum, smul_sub, Finset.smul_sum]
  have he : cpow (uLM D Sc i μ) b ≫ eLM D Sc i μ N = eLM D Sc i μ (b + N) :=
    cpow_uL_eL i μ b N
  have ht : ∀ j, cpow (uLM D Sc i μ) b ≫ eLM D Sc i μ j ≫
      dcM D Sc i μ j ≫ eLM D Sc i μ N =
      eLM D Sc i μ (b + j) ≫ dcM D Sc i μ j ≫ eLM D Sc i μ N := by
    intro j
    rw [← Category.assoc (cpow (uLM D Sc i μ) b) (eLM D Sc i μ j), cpow_uL_eL]
  simp only [he, ht, neg_smul]
  abel

private theorem paired_sign_isUnit (p : ZMod 2) : IsUnit (zsign k p) :=
  IsUnit.of_mul_eq_one _ (zsign_mul_self p)

theorem paired_target_pivot_isUnit (cs : CScalars Sc) (i : I) (μ : X) (m : ℕ) :
    IsUnit (-((zsign k (D.parity i)) ^ (m + 1)) * (cs.c μ i : k)) :=
  (((paired_sign_isUnit (k := k) (D.parity i)).pow (m + 1)).neg).mul (cs.c μ i).isUnit

theorem paired_source_pivot_isUnit (cs : CScalars Sc) (i : I) (μ : X) (m : ℕ) :
    IsUnit ((zsign k (D.parity i)) ^ m * (↑(cs.c μ i)⁻¹ : k)) :=
  ((paired_sign_isUnit (k := k) (D.parity i)).pow m).mul (cs.c μ i)⁻¹.isUnit

theorem paired_target_initial_pivot_isUnit (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    IsUnit (-((zsign k (D.parity i)) ^ b *
      (zsign k (ipar D i μ) * (cs.c μ i : k)))) :=
  (((paired_sign_isUnit (k := k) (D.parity i)).pow b).mul
    ((paired_sign_isUnit (k := k) (ipar D i μ)).mul (cs.c μ i).isUnit)).neg

theorem paired_source_initial_pivot_isUnit (cs : CScalars Sc) (i : I) (μ : X) (b : ℕ) :
    IsUnit (-((zsign k (D.parity i)) ^ b *
      (-(zsign k (D.parity i * (D.h i μ : ZMod 2)) * (↑(cs.c μ i)⁻¹ : k))))) :=
  (((paired_sign_isUnit (k := k) (D.parity i)).pow b).mul
    (((paired_sign_isUnit (k := k) (D.parity i * (D.h i μ : ZMod 2))).mul
      (cs.c μ i)⁻¹.isUnit).neg)).neg

/-- Both shifted inverse-block index orders are strictly below the pivot. -/
theorem paired_inverse_indices_lower (N b j : ℕ) (hj : j ∈ Finset.range N) :
    j + b < N + b ∧ b + j < b + N := by
  have := Finset.mem_range.mp hj
  omega

/-- Every dot-slide correction is below either opposite-height pivot. -/
theorem paired_slide_indices_lower (N b s : ℕ) (hs : s ∈ Finset.range b) :
    s < N + b ∧ s < b + N := by
  have := Finset.mem_range.mp hs
  omega
end OddMath.SKM

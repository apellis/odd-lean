import OddMath.QuiverHecke.CyclotomicAction.ELVIndependentSBoundaryDivision

/-! # Ordered independent-S products at even moving colour

The parity-zero monic-S algebra in DeformedBoundaryDivision (5).
The existing ordered S product acts on full old coefficients. Its top
coefficient detects the input bound, including zero old corners. No
support restriction on exterior coefficients or the other colours is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

private theorem evenS_twist_zero (v : List I) (c : Old D Sc cutoff v v) :
    oldTwist D Sc cutoff 0 v v c = c := by
  obtain ⟨c, rfl⟩ := (ideal D Sc cutoff v v).mkQ_surjective c
  change (ideal D Sc cutoff v v).mkQ (twist k 0 c) = _
  rw [twist_zero]

theorem independentSRightProduct_even_single (i : I) (hi : D.parity i = 0)
    (v : List I) (m : ℕ) (b : Old D Sc cutoff v v) :
    independentSRightProduct D Sc cutoff i v (Finsupp.single m b) =
      ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        Finsupp.single (n + m) (oldComp D Sc cutoff v v v b
          (independentOutputS D Sc cutoff i v n)) := by
  simp only [independentSRightProduct, LinearMap.sum_apply, LinearMap.comp_apply,
    inputCoefficientShift, Finsupp.lsum_single, Finsupp.lsingle_apply,
    Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro n _
  rw [hi, nsmul_zero, evenS_twist_zero]

theorem independentSRightProduct_even_high (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (m : ℕ)
    (hm : outputSDegree D i v ≤ m) :
    independentSRightProduct D Sc cutoff i v f m =
      ∑ n ∈ (independentOutputS D Sc cutoff i v).support,
        oldComp D Sc cutoff v v v (f (m - n)) (independentOutputS D Sc cutoff i v n) := by
  simp only [independentSRightProduct, LinearMap.sum_apply, LinearMap.comp_apply,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.mapRange.linearMap_apply,
    Finsupp.mapRange_apply, LinearMap.flip_apply]
  apply Finset.sum_congr rfl
  intro n hn
  have hnm : n ≤ m := by
    have h := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at h
    omega
  have he : m = n + (m - n) := by omega
  rw [he, inputCoefficientShift_apply_add]
  rw [hi, nsmul_zero, evenS_twist_zero]
  simp only [Nat.add_sub_cancel_left]

/-- The leading coefficient of the actual S product is the input coefficient,
with no nonzero-corner hypothesis. -/
theorem independentSRightProduct_even_top (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (M : ℕ)
    (hf : ∀ m, M < m → f m = 0) :
    independentSRightProduct D Sc cutoff i v f (M + outputSDegree D i v) = f M := by
  rw [independentSRightProduct_even_high D Sc cutoff i hi v f _ (by omega)]
  rw [Finset.sum_eq_single (outputSDegree D i v)]
  · rw [Nat.add_sub_cancel, independentOutputS_top]
    obtain ⟨b, hb⟩ := (ideal D Sc cutoff v v).mkQ_surjective (f M)
    rw [← hb, oldComp_mk, Category.comp_id]
  · intro n hn hne
    have h := independentOutputS_support D Sc cutoff i v hn
    rw [Finset.mem_range] at h
    rw [hf _ (by omega), map_zero, LinearMap.zero_apply]
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, map_zero]

/-- If the S product vanishes above B, each possible input coefficient above
B-D vanishes, phrased without truncated subtraction or a nonzero hypothesis. -/
theorem independentSRightProduct_even_detect_bound (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v) (B : ℕ)
    (hf : ∀ m, outputSDegree D i v ≤ m → B < m →
      independentSRightProduct D Sc cutoff i v f m = 0)
    (m : ℕ) (hm : B < m + outputSDegree D i v) : f m = 0 := by
  by_contra h
  have hs : f.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr h⟩
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hbound : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have hle := hmax m (Finsupp.mem_support_iff.mpr h)
  change m ≤ M at hle
  have ht := independentSRightProduct_even_top D Sc cutoff i hi v f M hbound
  rw [hf _ (by omega) (by omega)] at ht
  exact (Finsupp.mem_support_iff.mp hM) ht.symm

/-- A right S product cannot be supported strictly below the S bound unless
its input is zero. This includes D=0 and zero corners. -/
theorem independentSRightProduct_even_eq_zero_of_low (i : I) (hi : D.parity i = 0)
    (v : List I) (f : ℕ →₀ Old D Sc cutoff v v)
    (hf : ∀ m, outputSDegree D i v ≤ m → independentSRightProduct D Sc cutoff i v f m = 0) :
    f = 0 := by
  by_contra h
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr h
  obtain ⟨M, hM, hmax⟩ := f.support.exists_max_image id hs
  have hb : ∀ n, M < n → f n = 0 := by
    intro n hn
    by_contra hz
    have hh := hmax n (Finsupp.mem_support_iff.mpr hz)
    change n ≤ M at hh
    omega
  have ht := independentSRightProduct_even_top D Sc cutoff i hi v f M hb
  rw [hf _ (by omega)] at ht
  exact (Finsupp.mem_support_iff.mp hM) ht.symm

/-- Uniqueness of ordered S quotients and low remainders. -/
theorem independentS_even_division_unique (i : I) (hi : D.parity i = 0)
    (v : List I) (f g r s : ℕ →₀ Old D Sc cutoff v v)
    (hr : r.support ⊆ Finset.range (outputSDegree D i v))
    (hs : s.support ⊆ Finset.range (outputSDegree D i v))
    (h : independentSRightProduct D Sc cutoff i v f + r =
      independentSRightProduct D Sc cutoff i v g + s) : f = g ∧ r = s := by
  have hfg : f = g := by
    apply sub_eq_zero.mp
    apply independentSRightProduct_even_eq_zero_of_low D Sc cutoff i hi v (f - g)
    intro m hm
    have hz (a : ℕ →₀ Old D Sc cutoff v v)
        (ha : a.support ⊆ Finset.range (outputSDegree D i v)) : a m = 0 := by
      apply Finsupp.notMem_support_iff.mp
      intro hh
      have hh' := Finset.mem_range.mp (ha hh)
      omega
    have he := congrArg (fun a : ℕ →₀ Old D Sc cutoff v v => a m) h
    simp only [Finsupp.add_apply, hz r hr, hz s hs, add_zero] at he
    rw [map_sub, Finsupp.sub_apply, he, sub_self]
  refine ⟨hfg, ?_⟩
  rw [hfg] at h
  exact add_left_cancel h

end OddMath.QuiverHecke.ELVOld

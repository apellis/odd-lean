import OddMath.SKM.SpanBubbleSlides
import OddMath.SKM.BubbleAlgebra

/-!
# Positive-dot errors in bubble transport

The dot filtration on the actual one-strand SKM slide span, supporting the
constant-coefficient comparison required by the reduction of Brundan–Ellis,
*Super Kac–Moody 2-categories*, §8. Multiplication retains the super-interchange
sign and never decreases the number of open dots.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation Finset
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- Right-slide expressions with at least `N` open dots on the strand. -/
def dotSlideAtLeast (μ : X) (l : Letter I) (N : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])) :=
  Submodule.span k {f | ∃ (a : ℕ), N ≤ a ∧
    ∃ (γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])),
      IsBub cs (wt D μ []) γ ∧ (∃ p, γ ∈ closedPar D Sc (wt D μ []) p) ∧
      f = cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [l] [] [] [] γ}

theorem dotSlideAtLeast_zero (μ : X) (l : Letter I) :
    dotSlideAtLeast cs μ l 0 = slideSetR cs μ l := by
  unfold dotSlideAtLeast slideSetR
  congr 1
  ext f
  simp

theorem gen_mem_dotSlideAtLeast {μ : X} {l : Letter I} {N a : ℕ} (ha : N ≤ a)
    {γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hγ : IsBub cs (wt D μ []) γ) (hp : ∃ p, γ ∈ closedPar D Sc (wt D μ []) p) :
    cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [l] [] [] [] γ ∈
      dotSlideAtLeast cs μ l N :=
  Submodule.subset_span ⟨a, ha, γ, hγ, hp, rfl⟩

/-- Composition adds the lower bounds on open-dot count, even when the
coefficient factors are odd and their order matters. -/
theorem dotSlideAtLeast_comp {μ : X} {l : Letter I} {N M : ℕ}
    {f g : (pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])}
    (hf : f ∈ dotSlideAtLeast cs μ l N) (hg : g ∈ dotSlideAtLeast cs μ l M) :
    f ≫ g ∈ dotSlideAtLeast cs μ l (N + M) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, γ, hγ, ⟨p, hp⟩, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, hb, γ', hγ', ⟨q, hq⟩, rfl⟩ := hg
      have E := plcL_right_interchange (D := D) (Sc := Sc) μ [l]
        (show γ ∈ homPar D Sc (wt D μ []) [] [] p from hp) (sChain_dotsLay l b)
      rw [map_whL_nil_nil] at E
      have E2 : plcL D Sc μ [l] [] [] [] γ ≫ cl D Sc μ [l] [l] (dotsLay l b) =
          zsign k (p * parsum D (dotsLay l b)) •
            (cl D Sc μ [l] [l] (dotsLay l b) ≫ plcL D Sc μ [l] [] [] [] γ) := E
      have key : (cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [l] [] [] [] γ) ≫
          (cl D Sc μ [l] [l] (dotsLay l b) ≫ plcL D Sc μ [l] [] [] [] γ') =
          zsign k (p * parsum D (dotsLay l b)) •
            (cl D Sc μ [l] [l] (dotsLay l (a + b)) ≫ plcL D Sc μ [l] [] [] [] (γ ≫ γ')) := by
        rw [Category.assoc, ← Category.assoc (plcL D Sc μ [l] [] [] [] γ), E2, Linear.smul_comp,
          Linear.comp_smul, Category.assoc, ← Category.assoc (cl D Sc μ [l] [l] (dotsLay l a)),
          cl_comp (sChain_dotsLay l a) (sChain_dotsLay l b), dotsLay_add, plcL_comp]
      rw [key]
      exact Submodule.smul_mem _ _
        (gen_mem_dotSlideAtLeast cs (Nat.add_le_add ha hb) (hγ.comp hγ')
          ⟨_, comp_mem_closedPar hp hq⟩)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ hx

theorem positiveDots_comp_slide {μ : X} {l : Letter I}
    {f g : (pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])}
    (hf : f ∈ dotSlideAtLeast cs μ l 1) (hg : g ∈ slideSetR cs μ l) :
    f ≫ g ∈ dotSlideAtLeast cs μ l 1 := by
  rw [← dotSlideAtLeast_zero cs μ l] at hg
  simpa only [Nat.add_zero] using dotSlideAtLeast_comp cs (N := 1) (M := 0) hf hg

theorem slide_comp_positiveDots {μ : X} {l : Letter I}
    {f g : (pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])}
    (hf : f ∈ slideSetR cs μ l) (hg : g ∈ dotSlideAtLeast cs μ l 1) :
    f ≫ g ∈ dotSlideAtLeast cs μ l 1 := by
  rw [← dotSlideAtLeast_zero cs μ l] at hf
  simpa only [Nat.zero_add] using dotSlideAtLeast_comp cs (N := 0) (M := 1) hf hg

theorem dots_rbub_bubLs_mem_positive (μ : X) (j i : I) (r : ℕ) (hr : 0 < r) (m : ℤ) :
    cl D Sc μ [up j] [up j] (dotsL [] j [] r) ≫ rbub j μ (bubLs cs i (wt D μ []) m) ∈
      dotSlideAtLeast cs μ (up j) 1 :=
  gen_mem_dotSlideAtLeast cs (l := up j) (N := 1) (a := r) hr
    (isBub_bubLs cs i _ m) (bubLs_mem_closedPar cs i _ m)

/-- Same-color raw bubbles have their unchanged bubble as zero-dot term. -/
theorem same_bubLs_slide_difference (μ : X) (i : I) (n : ℕ) :
    lbub i μ (bubLs cs i (wt D μ [up i]) n) -
      rbub i μ (bubLs cs i (wt D μ []) n) ∈ dotSlideAtLeast cs μ (up i) 1 := by
  rcases zmod2_cases (D.parity i) with hi | hi
  · rw [eq_7_8 cs i μ hi n, Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_add, one_smul, sub_zero, dotsL,
      List.replicate_zero, cl_nil, Category.id_comp, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
      (dots_rbub_bubLs_mem_positive cs μ i i (r + 1) (by omega) _)
  · rw [eq_7_10 cs i μ hi n, Finset.sum_range_succ']
    simp only [Nat.cast_zero, mul_zero, zero_add, one_smul, sub_zero, dotsL,
      List.replicate_zero, cl_nil, Category.id_comp, add_sub_cancel_right]
    exact Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _
      (dots_rbub_bubLs_mem_positive cs μ i i (2 * (r + 1)) (by omega) _)

/-- The raw bubble slides have leading coefficient `t_ij`; every other term
has a strictly positive open-dot power. -/
theorem bubLs_slide_difference (μ : X) (i j : I) (n : ℕ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) -
      (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) ∈
      dotSlideAtLeast cs μ (up j) 1 := by
  by_cases hij : i = j
  · subst j
    simpa only [Sc.t_self, Units.val_one, one_smul] using same_bubLs_slide_difference cs μ i n
  · rcases eq_or_lt_of_le (D.d_nonneg hij) with hd | hd
    · rw [eq_7_14_corrected cs i j μ hij hd.symm n, sub_self]
      exact Submodule.zero_mem _
    · rw [eq_7_12_connected cs i j μ hij hd n]
      have hne : D.d j i ≠ 0 := fun h => (ne_of_gt hd) ((D.d_eq_zero_iff i j).mpr h)
      have hp : 0 < D.dn j i := by
        have hc := D.dn_cast (Ne.symm hij)
        have hn := D.d_nonneg (Ne.symm hij)
        omega
      have hA := Submodule.smul_mem (dotSlideAtLeast cs μ (up j) 1) (Sc.t j i : k)
        (dots_rbub_bubLs_mem_positive cs μ j i (D.dn j i) hp ((n : ℤ) - D.dn i j))
      have hB :
          (∑ p ∈ Ioo 0 (D.dn i j), ∑ q ∈ Ioo 0 (D.dn j i),
            Sc.s i j p q • (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
              rbub j μ (bubLs cs i (wt D μ []) ((n : ℤ) + p - D.dn i j)))) ∈
          dotSlideAtLeast cs μ (up j) 1 :=
        Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q hq =>
          Submodule.smul_mem _ _ (dots_rbub_bubLs_mem_positive cs μ j i q (mem_Ioo.mp hq).1 _)
      have H := Submodule.add_mem _ hA hB
      convert H using 1
      abel

theorem normalized_bubLs_slide_difference (μ : X) (i j : I) (n : ℕ) :
    lbub j μ ((↑(cs.c (wt D μ [up j]) i)⁻¹ : k) • bubLs cs i (wt D μ [up j]) n) -
      rbub j μ ((↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ []) n) ∈
      dotSlideAtLeast cs μ (up j) 1 := by
  have H := Submodule.smul_mem (dotSlideAtLeast cs μ (up j) 1)
    (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) (bubLs_slide_difference cs μ i j n)
  have he : (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) * (Sc.t i j : k) =
      (↑(cs.c (wt D μ []) i)⁻¹ : k) := by
    have hu : (cs.c (wt D μ [up j]) i)⁻¹ * Sc.t i j = (cs.c μ i)⁻¹ := by
      rw [c_wt_upj cs i j μ]
      group
    simpa only [Units.val_mul, wt_nil] using congrArg (fun z : kˣ => (z : k)) hu
  simpa only [smul_sub, smul_smul, he, lbub, rbub, map_smul] using H

/-- Every generator of full `SYM` slides with its unchanged normalized
coefficient as the zero-dot term. Distinct-color scalar normalization is
retained; no `t_ij = 1` assumption is made. -/
theorem betaSYMGen_slide_difference (μ : X) (j : I) (g : SYMGen D) :
    lbub j μ (betaSYMGen cs (wt D μ [up j]) g) -
      rbub j μ (betaSYMGen cs (wt D μ []) g) ∈ dotSlideAtLeast cs μ (up j) 1 := by
  cases g with
  | inl a =>
    obtain ⟨i, n⟩ := a
    by_cases hi : D.parity i = 0
    · simpa only [betaSYMGen, hi, ite_true, betaGen, Nat.cast_add, Nat.cast_one] using
        normalized_bubLs_slide_difference cs μ i j (n + 1)
    · simpa only [betaSYMGen, hi, ite_false, betaDGen, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one] using
        normalized_bubLs_slide_difference cs μ i j (2 * (n + 1))
  | inr i =>
    change lbub j μ (oddBubble cs i (wt D μ [up j])) -
      rbub j μ (oddBubble cs i (wt D μ [])) ∈ _
    rw [oddBubble_slide_up cs i j μ i.property, sub_self]
    exact Submodule.zero_mem _

theorem rbub_mem_slideSetR (μ : X) (j : I)
    {γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hγ : IsBub cs (wt D μ []) γ) : rbub j μ γ ∈ slideSetR cs μ (up j) := by
  unfold IsBub bubbleSpan at hγ
  induction hγ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    exact rbub_bubLs_mem cs μ j i n
  | algebraMap r =>
    have hr : algebraMap k (End ((pres D Sc).obj (ob D (wt D μ []) []))) r = r • 𝟙 _ :=
      Algebra.algebraMap_eq_smul_one r
    erw [hr]
    rw [rbub, map_smul, ← rbub, rbub_id, ← rbub_id j μ]
    exact Submodule.smul_mem _ _
      (plcL_mem_slideSetR (l := up j) IsBub.id ⟨0, id_mem_closedPar _⟩)
  | add x y _ _ hx hy => rw [rbub, map_add]; exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    show plcL D Sc μ [up j] [] [] [] (y ≫ x) ∈ _
    rw [plcL_comp]
    exact slideSetR_comp hy hx

theorem betaSYM_isBub (μ : X) (p : SYM D k) : IsBub cs μ (betaSYM cs μ p) := by
  change betaSYM cs μ p ∈ bubbleSpan cs μ
  rw [← betaSYM_range cs μ]
  exact ⟨p, rfl⟩

/-- Every full coefficient has unchanged zero-dot term after one upward slide. -/
theorem betaSYM_slide_difference (μ : X) (j : I) (p : SYM D k) :
    lbub j μ (betaSYM cs (wt D μ [up j]) p) -
      rbub j μ (betaSYM cs (wt D μ []) p) ∈ dotSlideAtLeast cs μ (up j) 1 := by
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) p
  change lbub j μ (betaSYM cs (wt D μ [up j]) (SYM.mk D k p)) -
      rbub j μ (betaSYM cs (wt D μ []) (SYM.mk D k p)) ∈ _
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, lbub, rbub]
    change r • lbub j μ (𝟙 _) - r • rbub j μ (𝟙 _) ∈ _
    rw [lbub_id, rbub_id, sub_self]
    exact Submodule.zero_mem _
  | grade1 g =>
    change lbub j μ (betaSYM cs _ (SYM.ι D k g)) - rbub j μ (betaSYM cs _ (SYM.ι D k g)) ∈ _
    simpa only [betaSYM_ι] using betaSYMGen_slide_difference cs μ j g
  | add p q hp hq =>
    rw [map_add, map_add, map_add]
    simp only [lbub, rbub, map_add]
    change (lbub j μ (betaSYM cs _ (SYM.mk D k p)) + lbub j μ (betaSYM cs _ (SYM.mk D k q))) -
      (rbub j μ (betaSYM cs _ (SYM.mk D k p)) + rbub j μ (betaSYM cs _ (SYM.mk D k q))) ∈ dotSlideAtLeast cs μ (up j) 1
    rw [add_sub_add_comm]
    exact Submodule.add_mem _ hp hq
  | mul p q hp hq =>
    have hL := lbub_mem_slideSetR cs μ j (betaSYM_isBub cs _ (SYM.mk D k p))
    have hR := rbub_mem_slideSetR cs μ j (betaSYM_isBub cs _ (SYM.mk D k q))
    have h₁ := positiveDots_comp_slide cs hq hL
    have h₂ := slide_comp_positiveDots cs hR hp
    rw [map_mul, map_mul, map_mul]
    have hleft : lbub j μ (betaSYM cs (wt D μ [up j]) (SYM.mk D k p) *
        betaSYM cs (wt D μ [up j]) (SYM.mk D k q)) =
        lbub j μ (betaSYM cs _ (SYM.mk D k q)) ≫ lbub j μ (betaSYM cs _ (SYM.mk D k p)) :=
      plcL_comp _ _ _ _ _
    have hright : rbub j μ (betaSYM cs (wt D μ []) (SYM.mk D k p) *
        betaSYM cs (wt D μ []) (SYM.mk D k q)) =
        rbub j μ (betaSYM cs _ (SYM.mk D k q)) ≫ rbub j μ (betaSYM cs _ (SYM.mk D k p)) :=
      plcL_comp _ _ _ _ _
    rw [hleft, hright]
    convert Submodule.add_mem _ h₁ h₂ using 1
    simp only [Preadditive.sub_comp, Preadditive.comp_sub]
    abel

/-- Actual evaluation of finitely many strictly positive dot powers with full coefficients. -/
def positiveDotExpansion (μ : X) (j : I) :
    ({n : ℕ // 0 < n} →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j])) :=
  Finsupp.lsum k (fun n =>
    { toFun := fun p => cl D Sc μ [up j] [up j] (dotsLay (up j) n.val) ≫
        rbub j μ (betaSYM cs (wt D μ []) p)
      map_add' := by intros; simp only [map_add, rbub, Preadditive.comp_add]
      map_smul' := by intros; simp only [map_smul, rbub, Linear.comp_smul, RingHom.id_apply] })

theorem positiveDotExpansion_single (μ : X) (j : I) (n : {n : ℕ // 0 < n}) (p : SYM D k) :
    positiveDotExpansion cs μ j (Finsupp.single n p) =
      cl D Sc μ [up j] [up j] (dotsLay (up j) n.val) ≫ rbub j μ (betaSYM cs (wt D μ []) p) :=
  Finsupp.lsum_single k _ n p

/-- The positive-dot error span has finite coefficient lifts; a global lift of
bubbles is neither selected nor assumed. -/
theorem dotSlideAtLeast_one_le_range (μ : X) (j : I) :
    dotSlideAtLeast cs μ (up j) 1 ≤ (positiveDotExpansion cs μ j).range := by
  apply Submodule.span_le.mpr
  rintro f ⟨a, ha, γ, hγ, _, rfl⟩
  change γ ∈ bubbleSpan cs (wt D μ []) at hγ
  rw [← betaSYM_range cs (wt D μ [])] at hγ
  obtain ⟨p, rfl⟩ := hγ
  exact ⟨Finsupp.single ⟨a, ha⟩ p, positiveDotExpansion_single cs μ j ⟨a, ha⟩ p⟩

/-- Finite full-SYM slide with prescribed, unchanged constant coefficient `p`.
No independence, field, finite-color, or scalar-normalization assumption is used. -/
theorem betaSYM_exists_positiveDotExpansion (μ : X) (j : I) (p : SYM D k) :
    ∃ z : {n : ℕ // 0 < n} →₀ SYM D k,
      lbub j μ (betaSYM cs (wt D μ [up j]) p) =
        rbub j μ (betaSYM cs (wt D μ []) p) + positiveDotExpansion cs μ j z := by
  obtain ⟨z, hz⟩ := dotSlideAtLeast_one_le_range cs μ j (betaSYM_slide_difference cs μ j p)
  exact ⟨z, by rw [hz]; abel⟩

end OddMath.SKM

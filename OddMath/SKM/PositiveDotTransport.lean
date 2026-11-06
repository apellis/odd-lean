import OddMath.SKM.SpanBubbleSlides
import OddMath.SKM.BubbleAlgebra
import OddMath.SKM.SYMLowerTwist

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

/-- The weight of an elementary bubble generator of colour `i`: one step of `e_{n+1}` is one
degree of a bubble for an even colour and two degrees for an odd colour. -/
def genWeight (D : Datum I X) (i : I) : ℕ := if D.parity i = 0 then 1 else 2

theorem genWeight_pos (D : Datum I X) (i : I) : 0 < genWeight D i := by
  unfold genWeight; split <;> omega

variable (Sc) in
/-- The coefficients of the lowering twist realized by one upward slide past an upward
`j`-strand: the zero-dot terms `t_{ij}⁻¹ s_{ij}^{p0}` of the bubble slide (7.12), indexed by the
lowered generator degree `s`, with `p = d_{ij} - w s` for the generator weight `w`. -/
def slideTwistCoeff (j i : I) (s : ℕ) : k :=
  if genWeight D i * s ≤ D.dn i j then
    (↑(Sc.t i j)⁻¹ : k) * Sc.s i j (D.dn i j - genWeight D i * s) 0 else 0

variable (Sc) in
/-- The algebra automorphism of `SYM` by which the coefficient of a bubble changes when it slides
up past an upward `j`-strand, up to terms with positive open dots. -/
def slideTwist (j : I) : SYM D k →ₐ[k] SYM D k := SYM.lowerTwist D k (slideTwistCoeff Sc j)

/-- The zero-dot part of the counterclockwise bubble slide (7.12) past an upward `j`-strand:
the leading term and the pure terms `s_{ij}^{p0}`. -/
def slideRow (μ : X) (i j : I) (n : ℤ) :
    (pres D Sc).obj (ob D μ [up j]) ⟶ (pres D Sc).obj (ob D μ [up j]) :=
  (Sc.t i j : k) • rbub j μ (bubLs cs i (wt D μ []) n) +
    ∑ p ∈ range (D.dn i j), Sc.s i j p 0 • rbub j μ (bubLs cs i (wt D μ []) (n + p - D.dn i j))

/-- The raw bubble slides agree with their zero-dot part up to terms with a strictly positive
open-dot power. The zero-dot part contains the pure terms `s_{ij}^{p0}` as well as the leading
coefficient `t_{ij}`. -/
theorem bubLs_slide_difference (μ : X) (i j : I) (n : ℕ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) - slideRow cs μ i j n ∈
      dotSlideAtLeast cs μ (up j) 1 := by
  by_cases hij : i = j
  · subst j
    have h0 : D.dn i i = 0 := by unfold Datum.dn; rw [D.d_self]; rfl
    simpa only [slideRow, h0, range_zero, sum_empty, add_zero, Sc.t_self, Units.val_one,
      one_smul] using same_bubLs_slide_difference cs μ i n
  · rcases eq_or_lt_of_le (D.d_nonneg hij) with hd | hd
    · have h0 : D.dn i j = 0 := by unfold Datum.dn; rw [← hd]; rfl
      rw [eq_7_14_corrected cs i j μ hij hd.symm n]
      simp only [slideRow, h0, range_zero, sum_empty, add_zero, sub_self]
      exact Submodule.zero_mem _
    · rw [eq_7_12_connected cs i j μ hij hd n]
      have hp : 0 < D.dn j i := by
        have hc := D.dn_cast (Ne.symm hij)
        have hn := D.d_nonneg (Ne.symm hij)
        have hne : D.d j i ≠ 0 := fun h => (ne_of_gt hd) ((D.d_eq_zero_iff i j).mpr h)
        omega
      obtain ⟨m, hm⟩ : ∃ m, D.dn j i = m + 1 := ⟨D.dn j i - 1, by omega⟩
      have h0 : cl D Sc μ [up j] [up j] (dotsL [] j [] 0) = 𝟙 _ := by
        simp only [dotsL, List.replicate_zero, List.append_nil, cl_nil]
      have E : (∑ p ∈ range (D.dn i j), ∑ q ∈ range (D.dn j i),
            Sc.s i j p q • (cl D Sc μ [up j] [up j] (dotsL [] j [] q) ≫
              rbub j μ (bubLs cs i (wt D μ []) ((n : ℤ) + p - D.dn i j)))) =
          (∑ p ∈ range (D.dn i j), ∑ q ∈ range m,
            Sc.s i j p (q + 1) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (q + 1)) ≫
              rbub j μ (bubLs cs i (wt D μ []) ((n : ℤ) + p - D.dn i j)))) +
          ∑ p ∈ range (D.dn i j),
            Sc.s i j p 0 • rbub j μ (bubLs cs i (wt D μ []) ((n : ℤ) + p - D.dn i j)) := by
        rw [hm, ← sum_add_distrib]
        refine sum_congr rfl fun p _ => ?_
        rw [sum_range_succ', h0, Category.id_comp]
      rw [E]
      have hA := Submodule.smul_mem (dotSlideAtLeast cs μ (up j) 1) (Sc.t j i : k)
        (dots_rbub_bubLs_mem_positive cs μ j i (D.dn j i) hp ((n : ℤ) - D.dn i j))
      have hB :
          (∑ p ∈ range (D.dn i j), ∑ q ∈ range m,
            Sc.s i j p (q + 1) • (cl D Sc μ [up j] [up j] (dotsL [] j [] (q + 1)) ≫
              rbub j μ (bubLs cs i (wt D μ []) ((n : ℤ) + p - D.dn i j)))) ∈
          dotSlideAtLeast cs μ (up j) 1 :=
        Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
          Submodule.smul_mem _ _ (dots_rbub_bubLs_mem_positive cs μ j i (q + 1) (by omega) _)
      convert Submodule.add_mem _ hA hB using 1
      simp only [slideRow]
      abel

/-- The normalized form of `bubLs_slide_difference`: the zero-dot part has the unchanged
normalized bubble and the pure terms with coefficients `t_{ij}⁻¹ s_{ij}^{p0}`. -/
theorem normalized_bubLs_slide_difference (μ : X) (i j : I) (N : ℕ) :
    lbub j μ ((↑(cs.c (wt D μ [up j]) i)⁻¹ : k) • bubLs cs i (wt D μ [up j]) N) -
      rbub j μ ((↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ []) N +
        ∑ p ∈ range (D.dn i j), ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p 0) •
          ((↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ []) ((N : ℤ) + p - D.dn i j))) ∈
      dotSlideAtLeast cs μ (up j) 1 := by
  have H := Submodule.smul_mem (dotSlideAtLeast cs μ (up j) 1)
    (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) (bubLs_slide_difference cs μ i j N)
  have hu : (cs.c (wt D μ [up j]) i)⁻¹ * Sc.t i j = (cs.c (wt D μ []) i)⁻¹ := by
    rw [c_wt_upj cs i j μ, wt_nil]
    group
  have he : (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) * (Sc.t i j : k) =
      (↑(cs.c (wt D μ []) i)⁻¹ : k) := by
    simpa only [Units.val_mul] using congrArg (fun z : kˣ => (z : k)) hu
  have ht : (↑(Sc.t i j)⁻¹ : k) * (Sc.t i j : k) = 1 := Units.inv_mul _
  have he2 (a : k) : (↑(Sc.t i j)⁻¹ : k) * a * (↑(cs.c (wt D μ []) i)⁻¹ : k) =
      (↑(cs.c (wt D μ [up j]) i)⁻¹ : k) * a := by
    rw [← he]
    linear_combination (a * (↑(cs.c (wt D μ [up j]) i)⁻¹ : k)) * ht
  convert H using 1
  simp only [slideRow, lbub, rbub, map_add, map_sum, map_smul, smul_sub, smul_add,
    Finset.smul_sum, smul_smul, he, he2]

/-- The image under `betaSYM` of the elementary generator `e_m` (with `e_0 = 1`). -/
theorem betaSYM_eUp (ν : X) (i : I) (m : ℕ) :
    betaSYM cs ν (SYM.eUp D k i m) =
      (↑(cs.c ν i)⁻¹ : k) • bubLs cs i ν ((genWeight D i * m : ℕ) : ℤ) := by
  cases m with
  | zero =>
    rw [mul_zero, Nat.cast_zero, bubLs_zero, smul_smul, Units.inv_mul, one_smul]
    change betaSYM cs ν 1 = _
    rw [map_one]
    rfl
  | succ m =>
    change betaSYM cs ν (SYM.ι D k (.inl (i, m))) = _
    rw [betaSYM_ι]
    by_cases hi : D.parity i = 0
    · simp only [betaSYMGen, genWeight, if_pos hi, betaGen, one_mul, Nat.cast_add, Nat.cast_one]
    · simp only [betaSYMGen, genWeight, if_neg hi, betaDGen, Nat.cast_mul, Nat.cast_ofNat,
        Nat.cast_add, Nat.cast_one]

/-- Every generator of `SYM` slides up past an upward `j`-strand with its coefficient changed
by the lowering twist `slideTwist`, up to terms with a strictly positive open-dot power. -/
theorem betaSYMGen_slide_difference (μ : X) (j : I) (g : SYMGen D) :
    lbub j μ (betaSYMGen cs (wt D μ [up j]) g) -
      rbub j μ (betaSYM cs (wt D μ []) (slideTwist Sc j (SYM.ι D k g))) ∈
      dotSlideAtLeast cs μ (up j) 1 := by
  cases g with
  | inl a =>
    obtain ⟨i, n⟩ := a
    have hL : betaSYMGen cs (wt D μ [up j]) (.inl (i, n)) =
        betaSYM cs (wt D μ [up j]) (SYM.eUp D k i (n + 1)) := (betaSYM_ι cs _ _).symm
    have hG : ∀ m : ℤ, m < 0 →
        (↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ []) m = 0 := fun m hm => by
      rw [bubLs_neg cs i _ hm, smul_zero]
    have hpar : ∀ p < D.dn i j, (↑(Sc.t i j)⁻¹ : k) * Sc.s i j p 0 ≠ 0 →
        genWeight D i ∣ D.dn i j - p := by
      intro p _ hc
      unfold genWeight
      rcases zmod2_cases (D.parity i) with hi | hi
      · rw [if_pos hi]
        exact one_dvd _
      · rw [if_neg (show ¬ D.parity i = 0 by rw [hi]; decide)]
        have hs : Sc.s i j p 0 ≠ 0 := fun h => hc (by rw [h, mul_zero])
        have h1 := (ScalarData.parity_of_ne_zero hs).1
        rw [hi, mul_one, ZMod.natCast_eq_zero_iff] at h1
        have h2 := parity_mul_dn D i j
        rw [hi, one_mul, ZMod.natCast_eq_zero_iff] at h2
        omega
    have hR : betaSYM cs (wt D μ []) (slideTwist Sc j (SYM.ι D k (.inl (i, n)))) =
        (↑(cs.c (wt D μ []) i)⁻¹ : k) •
            bubLs cs i (wt D μ []) ((genWeight D i * (n + 1) : ℕ) : ℤ) +
          ∑ p ∈ range (D.dn i j), ((↑(Sc.t i j)⁻¹ : k) * Sc.s i j p 0) •
            ((↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ [])
              (((genWeight D i * (n + 1) : ℕ) : ℤ) + p - D.dn i j)) := by
      rw [slideTwist, SYM.lowerTwist_ι]
      change betaSYM cs (wt D μ []) (SYM.lowerE D k (slideTwistCoeff Sc j) i (n + 1)) = _
      simp only [SYM.lowerE, map_add, map_sum, map_smul, betaSYM_eUp]
      congr 1
      exact sum_Ioc_shift_eq_sum_range (genWeight D i) (D.dn i j) (n + 1) (genWeight_pos D i)
        (fun p => (↑(Sc.t i j)⁻¹ : k) * Sc.s i j p 0)
        (fun m => (↑(cs.c (wt D μ []) i)⁻¹ : k) • bubLs cs i (wt D μ []) m) hG hpar
    rw [hL, hR, betaSYM_eUp]
    exact normalized_bubLs_slide_difference cs μ i j (genWeight D i * (n + 1))
  | inr i =>
    rw [slideTwist, SYM.lowerTwist_ι]
    change lbub j μ (oddBubble cs i (wt D μ [up j])) -
      rbub j μ (betaSYM cs (wt D μ []) (SYM.ι D k (.inr i))) ∈ _
    rw [betaSYM_ι]
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

/-- Every full coefficient slides up past an upward `j`-strand with its coefficient changed by
the lowering twist `slideTwist`, up to terms with a strictly positive open-dot power. -/
theorem betaSYM_slide_difference (μ : X) (j : I) (p : SYM D k) :
    lbub j μ (betaSYM cs (wt D μ [up j]) p) -
      rbub j μ (betaSYM cs (wt D μ []) (slideTwist Sc j p)) ∈ dotSlideAtLeast cs μ (up j) 1 := by
  obtain ⟨p, rfl⟩ := RingQuot.mkAlgHom_surjective k (SYMRel D k) p
  change lbub j μ (betaSYM cs (wt D μ [up j]) (SYM.mk D k p)) -
      rbub j μ (betaSYM cs (wt D μ []) (slideTwist Sc j (SYM.mk D k p))) ∈ _
  induction p using FreeAlgebra.induction with
  | grade0 r =>
    simp only [Algebra.algebraMap_eq_smul_one, map_smul, map_one, lbub, rbub]
    change r • lbub j μ (𝟙 _) - r • rbub j μ (𝟙 _) ∈ _
    rw [lbub_id, rbub_id, sub_self]
    exact Submodule.zero_mem _
  | grade1 g =>
    change lbub j μ (betaSYM cs _ (SYM.ι D k g)) -
      rbub j μ (betaSYM cs _ (slideTwist Sc j (SYM.ι D k g))) ∈ _
    rw [betaSYM_ι]
    exact betaSYMGen_slide_difference cs μ j g
  | add p q hp hq =>
    convert Submodule.add_mem _ hp hq using 1
    simp only [map_add, lbub, rbub]
    abel
  | mul p q hp hq =>
    have hL := lbub_mem_slideSetR cs μ j (betaSYM_isBub cs _ (SYM.mk D k p))
    have hR := rbub_mem_slideSetR cs μ j (betaSYM_isBub cs _ (slideTwist Sc j (SYM.mk D k q)))
    have h₁ := positiveDots_comp_slide cs hq hL
    have h₂ := slide_comp_positiveDots cs hR hp
    have hleft : lbub j μ (betaSYM cs (wt D μ [up j]) (SYM.mk D k (p * q))) =
        lbub j μ (betaSYM cs _ (SYM.mk D k q)) ≫ lbub j μ (betaSYM cs _ (SYM.mk D k p)) := by
      rw [map_mul, map_mul]
      exact plcL_comp _ _ _ _ _
    have hright : rbub j μ (betaSYM cs (wt D μ []) (slideTwist Sc j (SYM.mk D k (p * q)))) =
        rbub j μ (betaSYM cs _ (slideTwist Sc j (SYM.mk D k q))) ≫
          rbub j μ (betaSYM cs _ (slideTwist Sc j (SYM.mk D k p))) := by
      rw [map_mul, map_mul, map_mul]
      exact plcL_comp _ _ _ _ _
    rw [hleft, hright]
    convert Submodule.add_mem _ h₁ h₂ using 1
    simp only [Preadditive.sub_comp, Preadditive.comp_sub]
    abel

end OddMath.SKM

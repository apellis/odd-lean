/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.SpanBubbles
import OddMath.SKM.OddBubbleCentrality
import OddMath.SKM.SpanLower

/-!
# Bubbles slide across strands into the image of `β`

Infrastructure for J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Theorem 8.1 and the surjectivity of `β_λ` in (1.21)–(1.22): an element of the image of `β`
(`IsBub`, `OddMath.SKM.SpanBubbles`) placed next to a strand can be moved to the other side of
the strand, leaving dots on the strand. This is the form of the bubble slides of Proposition 7.3
used in the spanning argument (as in M. Khovanov, A. Lauda, *A categorification of quantum
`sl(n)`*, arXiv:0807.3250v1, §3.2.1).

For a strand `l` with rightmost region `μ`:

* `slideSetR cs μ l`: the span of `(a dots on l) ≫ (γ to the right of l)` with `γ` a homogeneous
  element of the image of `β_μ`;
* `slideSetL cs μ l`: the span of `(β to the left of l) ≫ (a dots on l)` with `β` a homogeneous
  element of the image of `β_{μ + l}`.

Both are closed under composition (`slideSetR_comp`, `slideSetL_comp`; super interchange law).
Dots on a downward strand are the downward dots (2.1) (`dotsLay`).

## Main results

* `lbub_mem_slideSetR`: an element of the image of `β` to the left of an upward strand `Eⱼ`
  slides to the right, by (7.8), (7.10), (7.12), (7.14) (Proposition 7.3, the last with the
  factor `tᵢⱼ` of the erratum).
* `rbub_mem_slideSetL`: one to the right of `Eⱼ` slides to the left, by (7.7), (7.9), (7.11),
  (7.13).
* `plcL_dn_mem_slideSetR`: one to the left of a downward strand `Fⱼ` slides to the right; this is
  the right mate (`bubbleMate`) of `rbub_mem_slideSetL`.
* `bubble_slide_right`: the two cases together, for any strand.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation Finset

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-! ## Dots on a strand -/

/-- `a` dots on a strand: upward dots on `Eⱼ`, downward dots (2.1) on `Fⱼ`. -/
def dotsLay : Letter I → ℕ → List (LayerData I)
  | (true, j), a => dotsL [] j [] a
  | (false, j), a => ddotsL j a

@[simp] theorem dotsLay_up (j : I) (a : ℕ) : dotsLay (up j) a = dotsL [] j [] a := rfl

@[simp] theorem dotsLay_dn (j : I) (a : ℕ) : dotsLay (dn j) a = ddotsL j a := rfl

theorem sChain_dotsLay (l : Letter I) (a : ℕ) : SChain [l] (dotsLay l a) [l] := by
  obtain ⟨_ | _, j⟩ := l
  · exact sChain_ddotsL j a
  · exact sChain_dotsL [] j [] a

theorem dotsLay_zero (l : Letter I) : dotsLay l 0 = [] := by
  obtain ⟨_ | _, j⟩ := l <;> rfl

theorem dotsLay_add (l : Letter I) (a b : ℕ) :
    dotsLay l a ++ dotsLay l b = dotsLay l (a + b) := by
  obtain ⟨_ | _, j⟩ := l
  · simp only [dotsLay, ddotsL, ← List.flatten_append, List.replicate_append_replicate]
  · simp only [dotsLay, dotsL, List.replicate_append_replicate]

theorem id_mem_closedPar (ν : X) : 𝟙 ((pres D Sc).obj (ob D ν [])) ∈ closedPar D Sc ν 0 := by
  rw [← cl_nil (D := D) (Sc := Sc) ν []]
  exact cl_mem_closedPar (L := []) rfl rfl

theorem bubLs_mem_closedPar (i : I) (ν : X) (n : ℤ) :
    ∃ p, bubLs cs i ν n ∈ closedPar D Sc ν p :=
  ⟨_, bubLs_mem cs i ν n⟩

theorem bubRs_mem_closedPar (i : I) (ν : X) (n : ℤ) :
    ∃ p, bubRs cs i ν n ∈ closedPar D Sc ν p :=
  ⟨_, bubR_mem cs i ν _⟩

/-! ## The slide sets -/

/-- The span of `(a dots on l) ≫ (γ to the right of l)`, `γ` homogeneous in the image of
`β_μ`. -/
def slideSetR (μ : X) (l : Letter I) :
    Submodule k ((pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])) :=
  Submodule.span k {f | ∃ (a : ℕ)
    (γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])),
    IsBub cs (wt D μ []) γ ∧ (∃ p, γ ∈ closedPar D Sc (wt D μ []) p) ∧
    f = cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [l] [] [] [] γ}

/-- The span of `(β to the left of l) ≫ (a dots on l)`, `β` homogeneous in the image of
`β_{μ + l}`. -/
def slideSetL (μ : X) (l : Letter I) :
    Submodule k ((pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])) :=
  Submodule.span k {f | ∃ (a : ℕ)
    (β : (pres D Sc).obj (ob D (wt D μ [l]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [l]) [])),
    IsBub cs (wt D μ [l]) β ∧ (∃ p, β ∈ closedPar D Sc (wt D μ [l]) p) ∧
    f = plcL D Sc μ [] [l] [] [] β ≫ cl D Sc μ [l] [l] (dotsLay l a)}

variable {cs}

theorem gen_mem_slideSetR {μ : X} {l : Letter I} (a : ℕ)
    {γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hγ : IsBub cs (wt D μ []) γ) (hp : ∃ p, γ ∈ closedPar D Sc (wt D μ []) p) :
    cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [l] [] [] [] γ ∈ slideSetR cs μ l :=
  Submodule.subset_span ⟨a, γ, hγ, hp, rfl⟩

theorem plcL_mem_slideSetR {μ : X} {l : Letter I}
    {γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hγ : IsBub cs (wt D μ []) γ) (hp : ∃ p, γ ∈ closedPar D Sc (wt D μ []) p) :
    plcL D Sc μ [l] [] [] [] γ ∈ slideSetR cs μ l := by
  have := gen_mem_slideSetR (l := l) 0 hγ hp
  rwa [dotsLay_zero, cl_nil, Category.id_comp] at this

theorem gen_mem_slideSetL {μ : X} {l : Letter I} (a : ℕ)
    {β : (pres D Sc).obj (ob D (wt D μ [l]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [l]) [])}
    (hβ : IsBub cs (wt D μ [l]) β) (hp : ∃ p, β ∈ closedPar D Sc (wt D μ [l]) p) :
    plcL D Sc μ [] [l] [] [] β ≫ cl D Sc μ [l] [l] (dotsLay l a) ∈ slideSetL cs μ l :=
  Submodule.subset_span ⟨a, β, hβ, hp, rfl⟩

theorem plcL_mem_slideSetL {μ : X} {l : Letter I}
    {β : (pres D Sc).obj (ob D (wt D μ [l]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [l]) [])}
    (hβ : IsBub cs (wt D μ [l]) β) (hp : ∃ p, β ∈ closedPar D Sc (wt D μ [l]) p) :
    plcL D Sc μ [] [l] [] [] β ∈ slideSetL cs μ l := by
  have := gen_mem_slideSetL (l := l) 0 hβ hp
  rw [dotsLay_zero, cl_nil] at this
  erw [Category.comp_id] at this
  exact this

/-- **The right slide set is closed under composition.** -/
theorem slideSetR_comp {μ : X} {l : Letter I}
    {f g : (pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])}
    (hf : f ∈ slideSetR cs μ l) (hg : g ∈ slideSetR cs μ l) : f ≫ g ∈ slideSetR cs μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, γ, hγ, ⟨p, hp⟩, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, γ', hγ', ⟨q, hq⟩, rfl⟩ := hg
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
        (gen_mem_slideSetR _ (hγ.comp hγ') ⟨_, comp_mem_closedPar hp hq⟩)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ hx

/-- **The left slide set is closed under composition.** -/
theorem slideSetL_comp {μ : X} {l : Letter I}
    {f g : (pres D Sc).obj (ob D μ [l]) ⟶ (pres D Sc).obj (ob D μ [l])}
    (hf : f ∈ slideSetL cs μ l) (hg : g ∈ slideSetL cs μ l) : f ≫ g ∈ slideSetL cs μ l := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, β, hβ, ⟨p, hp⟩, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨b, β', hβ', ⟨q, hq⟩, rfl⟩ := hg
      have E := plcL_left_interchange (D := D) (Sc := Sc) μ [l]
        (show β' ∈ homPar D Sc (wt D μ [l]) [] [] q from hq) (sChain_dotsLay l a)
      rw [map_whL_nil_nil] at E
      have E2 : plcL D Sc μ [] [l] [] [] β' ≫ cl D Sc μ [l] [l] (dotsLay l a) =
          zsign k (q * parsum D (dotsLay l a)) •
            (cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [] [l] [] [] β') := E
      have E3 : cl D Sc μ [l] [l] (dotsLay l a) ≫ plcL D Sc μ [] [l] [] [] β' =
          zsign k (q * parsum D (dotsLay l a)) •
            (plcL D Sc μ [] [l] [] [] β' ≫ cl D Sc μ [l] [l] (dotsLay l a)) := by
        rw [E2, smul_smul, zsign_mul_self', one_smul]
      have key : (plcL D Sc μ [] [l] [] [] β ≫ cl D Sc μ [l] [l] (dotsLay l a)) ≫
          (plcL D Sc μ [] [l] [] [] β' ≫ cl D Sc μ [l] [l] (dotsLay l b)) =
          zsign k (q * parsum D (dotsLay l a)) •
            (plcL D Sc μ [] [l] [] [] (β ≫ β') ≫ cl D Sc μ [l] [l] (dotsLay l (a + b))) := by
        rw [Category.assoc, ← Category.assoc (cl D Sc μ [l] [l] (dotsLay l a)), E3,
          Linear.smul_comp, Linear.comp_smul, Category.assoc, ← Category.assoc
            (plcL D Sc μ [] [l] [] [] β), ← plcL_comp,
          cl_comp (sChain_dotsLay l a) (sChain_dotsLay l b), dotsLay_add]
      rw [key]
      exact Submodule.smul_mem _ _
        (gen_mem_slideSetL _ (hβ.comp hβ') ⟨_, comp_mem_closedPar hp hq⟩)
    | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ hx
  | zero => rw [Limits.zero_comp]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [Linear.smul_comp]; exact Submodule.smul_mem _ _ hx

variable (cs)

/-! ## Upward strands -/

theorem dots_rbub_bubLs_mem (μ : X) (j i : I) (r : ℕ) (m : ℤ) :
    cl D Sc μ [up j] [up j] (dotsL [] j [] r) ≫ rbub j μ (bubLs cs i (wt D μ []) m) ∈
      slideSetR cs μ (up j) :=
  gen_mem_slideSetR (l := up j) r (isBub_bubLs cs i _ m) (bubLs_mem_closedPar cs i _ m)

theorem rbub_bubLs_mem (μ : X) (j i : I) (m : ℤ) :
    rbub j μ (bubLs cs i (wt D μ []) m) ∈ slideSetR cs μ (up j) :=
  plcL_mem_slideSetR (l := up j) (isBub_bubLs cs i _ m) (bubLs_mem_closedPar cs i _ m)

/-- A counterclockwise bubble to the left of `Eⱼ` slides to the right (Proposition 7.3,
(7.8), (7.10), (7.12), (7.14)). -/
theorem lbub_bubLs_mem_slideSetR (μ : X) (j i : I) (n : ℤ) :
    lbub j μ (bubLs cs i (wt D μ [up j]) n) ∈ slideSetR cs μ (up j) := by
  by_cases hij : i = j
  · subst hij
    rcases lt_or_ge n 0 with hn | hn
    · rw [bubLs_neg cs i _ hn, lbub, map_zero]; exact Submodule.zero_mem _
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rcases zmod2_cases (D.parity i) with hi | hi
    · rw [eq_7_8 cs i μ hi m]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (dots_rbub_bubLs_mem cs μ i i r _)
    · rw [eq_7_10 cs i μ hi m]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (dots_rbub_bubLs_mem cs μ i i _ _)
  · rcases eq_or_lt_of_le (D.d_nonneg hij) with hd | hd
    · rcases lt_or_ge n 0 with hn | hn
      · rw [bubLs_neg cs i _ hn, lbub, map_zero]; exact Submodule.zero_mem _
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [eq_7_14_corrected cs i j μ hij hd.symm m]
      exact Submodule.smul_mem _ _ (rbub_bubLs_mem cs μ j i _)
    · rw [eq_7_12_connected cs i j μ hij hd n]
      refine Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (rbub_bubLs_mem cs μ j i _))
        (Submodule.smul_mem _ _ (dots_rbub_bubLs_mem cs μ j i _ _)))
        (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
          Submodule.smul_mem _ _ (dots_rbub_bubLs_mem cs μ j i _ _))

theorem lbub_bubRs_dots_mem (μ : X) (j i : I) (r : ℕ) (m : ℤ) :
    lbub j μ (bubRs cs i (wt D μ [up j]) m) ≫ cl D Sc μ [up j] [up j] (dotsL [] j [] r) ∈
      slideSetL cs μ (up j) :=
  gen_mem_slideSetL (l := up j) r (isBub_bubRs cs i _ m) (bubRs_mem_closedPar cs i _ m)

theorem lbub_bubRs_mem (μ : X) (j i : I) (m : ℤ) :
    lbub j μ (bubRs cs i (wt D μ [up j]) m) ∈ slideSetL cs μ (up j) :=
  plcL_mem_slideSetL (l := up j) (isBub_bubRs cs i _ m) (bubRs_mem_closedPar cs i _ m)

/-- A clockwise bubble to the right of `Eⱼ` slides to the left (Proposition 7.3, (7.7), (7.9),
(7.11), (7.13)). -/
theorem rbub_bubRs_mem_slideSetL (μ : X) (j i : I) (n : ℤ) :
    rbub j μ (bubRs cs i (wt D μ []) n) ∈ slideSetL cs μ (up j) := by
  by_cases hij : i = j
  · subst hij
    rcases lt_or_ge n 0 with hn | hn
    · rw [bubRs_neg cs i _ hn, rbub, map_zero]; exact Submodule.zero_mem _
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rcases zmod2_cases (D.parity i) with hi | hi
    · rw [eq_7_7 cs i μ hi m]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (lbub_bubRs_dots_mem cs μ i i r _)
    · rw [eq_7_9 cs i μ hi m]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (lbub_bubRs_dots_mem cs μ i i _ _)
  · rcases eq_or_lt_of_le (D.d_nonneg hij) with hd | hd
    · rcases lt_or_ge n 0 with hn | hn
      · rw [bubRs_neg cs i _ hn, rbub, map_zero]; exact Submodule.zero_mem _
      obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [eq_7_13_corrected cs i j μ hij hd.symm m]
      exact Submodule.smul_mem _ _ (lbub_bubRs_mem cs μ j i _)
    · rw [eq_7_11_connected cs i j μ hij hd n]
      refine Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ (lbub_bubRs_mem cs μ j i _))
        (Submodule.smul_mem _ _ (lbub_bubRs_dots_mem cs μ j i _ _)))
        (Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ =>
          Submodule.smul_mem _ _ (lbub_bubRs_dots_mem cs μ j i _ _))

/-- **Bubbles slide to the right across an upward strand**: an element of the image of `β` to
the left of `Eⱼ` is a combination of dots on `Eⱼ` followed by elements of the image of `β` to
its right. -/
theorem lbub_mem_slideSetR (μ : X) (j : I)
    {β : (pres D Sc).obj (ob D (wt D μ [up j]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [up j]) [])}
    (hβ : IsBub cs (wt D μ [up j]) β) : lbub j μ β ∈ slideSetR cs μ (up j) := by
  unfold IsBub bubbleSpan at hβ
  induction hβ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    exact lbub_bubLs_mem_slideSetR cs μ j i n
  | algebraMap r =>
    have hr : algebraMap k (End ((pres D Sc).obj (ob D (wt D μ [up j]) []))) r = r • 𝟙 _ :=
      Algebra.algebraMap_eq_smul_one r
    erw [hr]
    rw [lbub, map_smul, ← lbub, lbub_id, ← rbub_id j μ]
    exact Submodule.smul_mem _ _
      (plcL_mem_slideSetR (l := up j) IsBub.id ⟨0, id_mem_closedPar _⟩)
  | add x y _ _ hx hy => rw [lbub, map_add]; exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    show plcL D Sc μ [] [up j] [] [] (y ≫ x) ∈ _
    rw [plcL_comp]
    exact slideSetR_comp hy hx

/-- **Bubbles slide to the left across an upward strand.** -/
theorem rbub_mem_slideSetL (μ : X) (j : I)
    {γ : (pres D Sc).obj (ob D (wt D μ []) []) ⟶ (pres D Sc).obj (ob D (wt D μ []) [])}
    (hγ : IsBub cs (wt D μ []) γ) : rbub j μ γ ∈ slideSetL cs μ (up j) := by
  unfold IsBub at hγ
  rw [bubbleSpan_eq_adjoin_bubRs] at hγ
  induction hγ using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨i, n, rfl⟩ := hx
    exact rbub_bubRs_mem_slideSetL cs μ j i n
  | algebraMap r =>
    have hr : algebraMap k (End ((pres D Sc).obj (ob D (wt D μ []) []))) r = r • 𝟙 _ :=
      Algebra.algebraMap_eq_smul_one r
    erw [hr]
    rw [rbub, map_smul, ← rbub, rbub_id, ← lbub_id j μ]
    exact Submodule.smul_mem _ _
      (plcL_mem_slideSetL (l := up j) IsBub.id ⟨0, id_mem_closedPar _⟩)
  | add x y _ _ hx hy => rw [rbub, map_add]; exact Submodule.add_mem _ hx hy
  | mul x y _ _ hx hy =>
    show plcL D Sc μ [up j] [] [] [] (y ≫ x) ∈ _
    rw [plcL_comp]
    exact slideSetL_comp hy hx

/-! ## Downward strands, by the right mate -/

theorem IsBub.regionCast {ν ν' : X} (h : ν = ν')
    {β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])} (hβ : IsBub cs ν β) :
    IsBub cs ν' (regionCast h β) := by
  subst h; exact hβ

theorem regionCast_mem_closedPar {ν ν' : X} (h : ν = ν') {p : ZMod 2}
    {β : (pres D Sc).obj (ob D ν []) ⟶ (pres D Sc).obj (ob D ν [])}
    (hβ : β ∈ closedPar D Sc ν p) : regionCast h β ∈ closedPar D Sc ν' p := by
  subst h; exact hβ

theorem wt_dn_up (j : I) (μ : X) : wt D (wt D μ [dn j]) [up j] = wt D μ [] := by
  simp [wt, sh]

/-- The right mate of a 2-morphism to the right of `Eⱼ` is the same 2-morphism to the left of
`Fⱼ`. -/
theorem bubbleMate_rbub (j : I) (μ : X)
    (γ : (pres D Sc).obj (ob D (wt D μ [dn j]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [dn j]) [])) :
    bubbleMate (Sc := Sc) j μ (rbub j (wt D μ [dn j]) γ) = plcL D Sc μ [] [dn j] [] [] γ := by
  have hγ := mem_span_cl (D := D) (Sc := Sc) (wt D μ [dn j]) γ
  induction hγ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl⟩ := hf
    unfold rbub
    erw [plcL_cl, bubbleMate_cl, plcL_cl]
    exact mate_closed_right j μ hL
  | zero => unfold rbub; erw [map_zero, map_zero, map_zero]
  | add x y _ _ hx hy =>
    unfold rbub at *
    erw [map_add, map_add, map_add, hx, hy]
  | smul a x _ hx =>
    unfold rbub at *
    erw [map_smul, map_smul, map_smul, hx]

/-- The right mate of `(β to the left of Eⱼ) ≫ (a dots)`, `β` homogeneous: up to a sign,
`(a downward dots) ≫ (β to the right of Fⱼ)`. -/
theorem bubbleMate_lbub_dots (j : I) (μ : X) {p : ZMod 2}
    {β : (pres D Sc).obj (ob D (wt D (wt D μ [dn j]) [up j]) []) ⟶
      (pres D Sc).obj (ob D (wt D (wt D μ [dn j]) [up j]) [])}
    (hβ : β ∈ closedPar D Sc (wt D (wt D μ [dn j]) [up j]) p) (a : ℕ) :
    bubbleMate (Sc := Sc) j μ (lbub j (wt D μ [dn j]) β ≫
        cl D Sc (wt D μ [dn j]) [up j] [up j] (dotsL [] j [] a)) =
      (zsign k (parsum D (dotsL [] j [] a) * p) *
          zsign k (D.parity j * ((a / 2 : ℕ) : ZMod 2))) •
        (cl D Sc μ [dn j] [dn j] (ddotsL j a) ≫
          plcL D Sc μ [dn j] [] [] [] (regionCast (wt_dn_up j μ) β)) := by
  induction hβ using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨L, hL, rfl, rfl⟩ := hf
    have hA : SChain [up j] (L.map (whL [] [up j])) [up j] := by simpa using hL.whisk [] [up j]
    have hB : SChain [up j] (dotsL [] j [] a) [up j] := sChain_dotsL [] j [] a
    have e1 : lbub j (wt D μ [dn j]) (cl D Sc _ [] [] L) ≫
        cl D Sc (wt D μ [dn j]) [up j] [up j] (dotsL [] j [] a) =
        cl D Sc (wt D μ [dn j]) [up j] [up j] (L.map (whL [] [up j]) ++ dotsL [] j [] a) := by
      unfold lbub
      erw [plcL_cl]
      exact cl_comp hA hB
    have e2 := cl_mate_comp Sc j μ hB hA
    have e3 := cl_ddot_pow Sc j μ a
    rw [← cl_ddotsL] at e3
    have e4 : cl D Sc μ [dn j] [dn j] (mateL j (dotsL [] j [] a)) =
        zsign k (D.parity j * ((a / 2 : ℕ) : ZMod 2)) • cl D Sc μ [dn j] [dn j] (ddotsL j a) := by
      rw [e3, smul_smul, zsign_mul_self', one_smul]
    have e5 : cl D Sc μ [dn j] [dn j] (mateL j (L.map (whL [] [up j]) ++ dotsL [] j [] a)) =
        zsign k (parsum D (dotsL [] j [] a) * parsum D (L.map (whL [] [up j]))) •
          cl D Sc μ [dn j] [dn j] (mateL j (dotsL [] j [] a) ++ mateL j (L.map (whL [] [up j]))) := by
      rw [e2, smul_smul, zsign_mul_self', one_smul]
    rw [e1, bubbleMate_cl, e5, ← cl_comp (sChain_mateL j hB) (sChain_mateL j hA), e4,
      mate_closed_left j μ hL, regionCast_cl, parsum_map_whL, Linear.smul_comp, smul_smul]
    congr 2
    erw [plcL_cl]
    rfl
  | zero =>
    unfold lbub
    rw [map_zero, Limits.zero_comp, map_zero, regionCast_zero, map_zero, Limits.comp_zero,
      smul_zero]
  | add x y _ _ hx hy =>
    unfold lbub at *
    rw [map_add, Preadditive.add_comp, map_add, hx, hy, regionCast_add, map_add,
      Preadditive.comp_add, smul_add]
  | smul r x _ hx =>
    unfold lbub at *
    rw [map_smul, Linear.smul_comp, map_smul, hx, regionCast_smul, map_smul, Linear.comp_smul,
      smul_comm]

/-- **Bubbles slide to the right across a downward strand**: the right mate of
`rbub_mem_slideSetL`. -/
theorem plcL_dn_mem_slideSetR (μ : X) (j : I)
    {β : (pres D Sc).obj (ob D (wt D μ [dn j]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [dn j]) [])}
    (hβ : IsBub cs (wt D μ [dn j]) β) : plcL D Sc μ [] [dn j] [] [] β ∈ slideSetR cs μ (dn j) := by
  rw [← bubbleMate_rbub j μ β]
  suffices H : ∀ f ∈ slideSetL cs (wt D μ [dn j]) (up j), bubbleMate (Sc := Sc) j μ f ∈
      slideSetR cs μ (dn j) from H _ (rbub_mem_slideSetL cs (wt D μ [dn j]) j hβ)
  intro f hf
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, β', hβ', ⟨p, hp⟩, rfl⟩ := hf
    have E := bubbleMate_lbub_dots (Sc := Sc) j μ hp a
    unfold lbub at E
    rw [dotsLay_up, E]
    exact Submodule.smul_mem _ _ (gen_mem_slideSetR (l := dn j) a
      (hβ'.regionCast cs _) ⟨p, regionCast_mem_closedPar _ hp⟩)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul r x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/-- **Bubbles slide to the right across any strand**: an element of the image of `β_{μ + l}`
to the left of the strand `l` (rightmost region `μ`) is a linear combination of (dots on `l`) ≫
(homogeneous elements of the image of `β_μ` to the right of `l`). -/
theorem bubble_slide_right (μ : X) (l : Letter I)
    {β : (pres D Sc).obj (ob D (wt D μ [l]) []) ⟶ (pres D Sc).obj (ob D (wt D μ [l]) [])}
    (hβ : IsBub cs (wt D μ [l]) β) : plcL D Sc μ [] [l] [] [] β ∈ slideSetR cs μ l := by
  obtain ⟨_ | _, j⟩ := l
  · exact plcL_dn_mem_slideSetR cs μ j hβ
  · exact lbub_mem_slideSetR cs μ j hβ

end OddMath.SKM

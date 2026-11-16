/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.BubbleGrading
import OddMath.SKM.BubbleCoefficientGrading
import OddMath.SKM.Nondegeneracy
import OddMath.SKM.ScalarChangeCoefficientBasis
import OddMath.SKM.GradedParameters
import OddMath.Diagrams.CoefficientGradedSupercategory

/-!
# Homogeneous bases for the coefficient grading

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, "Gradings",
and the Nondegeneracy Conjecture of §8; J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2,
§2.2 (parameters over a graded ring) and Theorem 5.6 (bases of graded Hom spaces).

Let the ground ring `k` be graded by `𝒜 : ℤ → Submodule K k`. The *total coefficient grading*
of the 2-supercategory `𝔘(𝔤)` (`OddMath.Diagrams.CoefficientGrading`) gives a sum
`Σ r_g g` of diagrams degree `d` when each `r_g` has degree `d - deg g`, with the generator
degrees `gdeg` of the table after (1.31); its degree-`d` part of a Hom group is
`presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b d`.

If the bubble normalizations `c_{λ;i}` and their inverses have degree `0`, the decorated
matching `F_t` times the coefficient monomial `b_a` of `SYM` (`SYM.coefficientBasis`) lies in
degree `deg b_a + deg F_t`, where `deg b_a` is `SYM.coefficientDegree` and `deg F_t` is the
table degree of the diagram (`expansion_single_coefficientBasis_mem`). More generally a
coefficient `r b_a` with `r ∈ 𝒜 e` gives degree `e + deg b_a + deg F_t`. So when the
decorated family is a basis (`MatchingBasisChoice.IsBasis`), the products `F_t b_a` form a
`k`-basis of the Hom group (`MatchingBasisChoice.homogeneousBasis`) consisting of elements
homogeneous for the total coefficient grading.

Under the graded parameter conditions (the `tᵢⱼ` of degree `0`, each nonzero `sᵢⱼ^{pq}` of
coefficient degree `2(dᵢdᵢⱼ - dᵢp - dⱼq)`), every relation of Definition 1.5 lies in one degree
(`isHomogeneous_coefficientGraded`), so for a graded algebra `𝒜` each Hom group is the internal
direct sum of its homogeneous parts (`iSupIndep_coefficientGraded`). Membership of the basis
elements needs no condition on the relations.

## Main results

* `SKM.expansion_single_smul_coefficientBasis_mem`, `SKM.expansion_single_coefficientBasis_mem`:
  the basis elements are homogeneous.
* `SKM.MatchingBasisChoice.homogeneousBasis`: under `IsBasis`, the `k`-basis `F_t b_a`.
* `SKM.isHomogeneous_coefficientGraded`, `SKM.iSupIndep_coefficientGraded`: the coefficient
  grading of `𝔘(𝔤)` with graded parameters.
-/

noncomputable section

namespace OddMath.Diagrams.CoefficientGrading

open CategoryTheory StringDiagrams

universe w v u₀ u₁ u₂

variable {S : Signature.{u₀, u₁, u₂}} {A : Type*} [AddCommGroup A]
  {K : Type*} [CommRing K] {R : Type w} [CommRing R] [Algebra K R]
  {𝒜 : A → Submodule K R} {deg : S.Gen → A} [SetLike.GradedMonoid 𝒜]
  {P : Presentation.{w, v} S R} {a b c : Obj S}

/-- A single diagram has its degree. -/
theorem diag_mem_presentedPart {g : a ⟶ b} {d : A} (hd : Diagram.degree deg g = d) :
    P.diag g ∈ presentedPart 𝒜 deg P a b d :=
  lin_mem_presentedPart (of_mem_part' g hd)

/-- A scalar of degree `e` shifts degrees by `e`; only the graded multiplication is used. -/
theorem smul_mem_presentedPart_of_mem {r : R} {e : A} (hr : r ∈ 𝒜 e) {x : P.obj a ⟶ P.obj b}
    {d : A} (hx : x ∈ presentedPart 𝒜 deg P a b d) :
    r • x ∈ presentedPart 𝒜 deg P a b (e + d) := by
  obtain ⟨f, hf, rfl⟩ := mem_presentedPart_iff.mp hx
  rw [← P.lin_smul]
  exact lin_mem_presentedPart (smul_mem_part hr hf)

/-- A scalar of degree `0` preserves degrees; only the graded multiplication is used. -/
theorem smul_mem_presentedPart_of_mem_zero {r : R} (hr : r ∈ 𝒜 0) {x : P.obj a ⟶ P.obj b}
    {d : A} (hx : x ∈ presentedPart 𝒜 deg P a b d) :
    r • x ∈ presentedPart 𝒜 deg P a b d := by
  simpa using smul_mem_presentedPart_of_mem hr hx

end OddMath.Diagrams.CoefficientGrading

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation LinDiagram OddMath.Diagrams
  OddMath.Diagrams.CoefficientGrading

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {K : Type*} [CommRing K] {k : Type w} [CommRing k] [Algebra K k]
  (sy : Symmetrizer D) {𝒜 : ℤ → Submodule K k} [SetLike.GradedMonoid 𝒜]

theorem zsign_mem_graded (p : ZMod 2) : zsign k p ∈ 𝒜 0 := by
  unfold zsign
  split_ifs
  · exact neg_mem SetLike.GradedOne.one_mem
  · exact SetLike.GradedOne.one_mem

theorem zsign_mul_mem_zero (p : ZMod 2) {c : k} (hc : c ∈ 𝒜 0) : zsign k p * c ∈ 𝒜 0 := by
  simpa using SetLike.GradedMul.mul_mem (zsign_mem_graded (𝒜 := 𝒜) p) hc

theorem neg_zsign_mul_mem_zero (p : ZMod 2) {c : k} (hc : c ∈ 𝒜 0) : -zsign k p * c ∈ 𝒜 0 := by
  simpa using SetLike.GradedMul.mul_mem (neg_mem (zsign_mem_graded (𝒜 := 𝒜) p)) hc

/-! ## Homogeneity of the relations -/

section Relations

variable (D) (𝒜)

theorem dg_mem_cpart {μ : X} {t t' : List (Letter I)} {ls : List (LayerData I)}
    {h : SChain t ls t'} {d : ℤ} (hd : gsum D sy μ ls = d) :
    dg (k := k) D μ ls h ∈ part 𝒜 (gdeg D sy) (ob D μ t) (ob D μ t') d :=
  of_mem_part' _ (by rw [degree_gdeg_mkD]; exact hd)

theorem idg_mem_cpart (μ : X) (t : List (Letter I)) :
    idg (k := k) D μ t ∈ part 𝒜 (gdeg D sy) (ob D μ t) (ob D μ t) 0 :=
  of_mem_part' _ (Diagram.degree_id _ _)

theorem smul_dg_mem_cpart {μ : X} {t t' : List (Letter I)} {ls : List (LayerData I)}
    {h : SChain t ls t'} {r : k} {m d : ℤ} (hr : r ∈ 𝒜 m) (hd : m + gsum D sy μ ls = d) :
    r • dg (k := k) D μ ls h ∈ part 𝒜 (gdeg D sy) (ob D μ t) (ob D μ t') d := by
  subst hd; exact smul_mem_part hr (dg_mem_cpart D sy 𝒜 rfl)

variable {D 𝒜}

omit [SetLike.GradedMonoid 𝒜] in
theorem zGate_mem_part {a b : Obj (sig D)} (i : I) {f : LinDiagram k a b} {d : ℤ}
    (hf : D.parity i = 1 → f ∈ part 𝒜 (gdeg D sy) a b d) :
    zGate D i f ∈ part 𝒜 (gdeg D sy) a b d := by
  unfold zGate
  split_ifs with h
  · exact hf h.1
  · exact zero_mem _

variable (D 𝒜)

/-- **Graded parameters for `𝔘(𝔤)`.** If the `tᵢⱼ` have degree `0` and every nonzero
`sᵢⱼ^{pq}` has its coefficient degree `2(dᵢdᵢⱼ - dᵢp - dⱼq)`, every relation of Definition 1.5
(and of the integral form) lies in one degree for the coefficient grading with generator
degrees `gdeg`. -/
theorem isHomogeneous_coefficientGraded {Ptwo : Prop} (Sc : ScalarData D k Ptwo)
    (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (coefficientDegree sy i j p q)) :
    CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc) := by
  intro r
  cases r with
  | quadEq i ν =>
    exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | quadZero i j ν _ hd =>
    refine ⟨0, sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_mem_part_zero (ht i j) (idg_mem_cpart D sy 𝒜 _ _))⟩
    rw [gsum_append, gsum_crossL, gsum_crossL, hd, (D.d_eq_zero_iff i j).mp hd]; ring
  | quadNe i j ν hij hd =>
    refine ⟨2 * (sy.d i * D.d i j), sub_mem (sub_mem (sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_dg_mem_cpart D sy 𝒜 (ht i j) ?_)) (smul_dg_mem_cpart D sy 𝒜 (ht j i) ?_))
      (sum_mem fun p hp => sum_mem fun q hq => ?_)⟩
    · rw [gsum_append, gsum_crossL, gsum_crossL]; have := sy.symm i j; linarith
    · rw [gsum_dotsL, dn_cast' hij]; ring
    · rw [gsum_dotsL, dn_cast' (Ne.symm hij)]; have := sy.symm i j; linarith
    · by_cases h0 : Sc.s i j p q = 0
      · rw [h0, zero_smul]; exact zero_mem _
      · rw [Finset.mem_range] at hp hq
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq
        refine smul_dg_mem_cpart D sy 𝒜 (hs i j p q hij hp' hq' h0) ?_
        rw [gsum_append, gsum_dotsL, gsum_dotsL, coefficientDegree]; ring
  | slideL i j ν _ =>
    refine ⟨2 * sy.d i + sy.d i * D.d i j, sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideLEq i ν =>
    refine ⟨0, sub_mem (sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)) (idg_mem_cpart D sy 𝒜 _ _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | slideR i j ν _ =>
    refine ⟨2 * sy.d j + sy.d i * D.d i j, sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideREq i ν =>
    refine ⟨0, sub_mem (sub_mem (dg_mem_cpart D sy 𝒜 ?_)
      (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)) (idg_mem_cpart D sy 𝒜 _ _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | braid i j k' ν _ =>
    refine ⟨sy.d i * D.d i j + sy.d i * D.d i k' + sy.d j * D.d j k',
      sub_mem (dg_mem_cpart D sy 𝒜 ?_) (dg_mem_cpart D sy 𝒜 ?_)⟩
    all_goals (simp only [gsum_append, gsum_crossL]; try ring)
  | braidEq i j ν hij =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j) - 2 * sy.d i, sub_mem (sub_mem
      (sub_mem (dg_mem_cpart D sy 𝒜 ?_) (dg_mem_cpart D sy 𝒜 ?_))
      (sum_mem fun s hs' => smul_dg_mem_cpart D sy 𝒜
        (by
          have := SetLike.GradedMul.mul_mem
            (zsign_mem_graded (𝒜 := 𝒜) (D.parity i * (D.parity j + s))) (ht i j)
          rwa [add_zero] at this) ?_))
      (sum_mem fun p hp => sum_mem fun q hq => sum_mem fun s hs' => ?_)⟩
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · rw [Finset.mem_range] at hs'
      rw [gsum_append, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        dn_cast' hij]
      push_cast; ring
    · by_cases hz : Sc.s i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact zero_mem _
      · rw [Finset.mem_range] at hp hq
        rw [Finset.mem_range] at hs'
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq
        refine smul_dg_mem_cpart D sy 𝒜
          (SetLike.GradedMul.mul_mem (zsign_mem_graded _) (hs i j p q hij hp' hq' hz)) ?_
        rw [gsum_append, gsum_append, gsum_dotsL, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega),
          Nat.cast_sub (by omega), coefficientDegree]
        push_cast; ring
  | zigE i ν =>
    refine ⟨0, sub_mem (dg_mem_cpart D sy 𝒜 ?_) (idg_mem_cpart D sy 𝒜 _ _)⟩
    simp [gsum, gdeg, Datum.d_self]; ring
  | zigF i ν =>
    refine ⟨0, sub_mem (dg_mem_cpart D sy 𝒜 ?_) (idg_mem_cpart D sy 𝒜 _ _)⟩
    simp [gsum, gdeg, Datum.d_self]; ring
  | invNe₁ i j ν _ =>
    exact ⟨0, sub_mem (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp))
      (idg_mem_cpart D sy 𝒜 _ _)⟩
  | invNe₂ i j ν _ =>
    exact ⟨0, sub_mem (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp))
      (idg_mem_cpart D sy 𝒜 _ _)⟩
  | invP₁ i ν _ =>
    refine ⟨0, sub_mem (add_mem (neg_mem
      (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp)))
      (sum_mem fun n _ => dg_mem_cpart D sy 𝒜 ?_)) (idg_mem_cpart D sy 𝒜 _ _)⟩
    rw [gsum_append, gsum_epsL, gsum_dcupL]; ring
  | invP₂ i ν _ =>
    exact ⟨0, add_mem (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp))
      (idg_mem_cpart D sy 𝒜 _ _)⟩
  | invP₃ i ν m _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | invP₄ i ν n _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | invP₅ i ν m n _ _ =>
    refine ⟨2 * sy.d i * (m - n), sub_mem (dg_mem_cpart D sy 𝒜 ?_) ?_⟩
    · rw [gsum_append, gsum_epsL, gsum_dcupL]; ring
    · split_ifs with hmn
      · subst hmn; rw [sub_self, mul_zero]; exact idg_mem_cpart D sy 𝒜 _ _
      · exact zero_mem _
  | invM₁ i ν _ =>
    refine ⟨0, sub_mem (add_mem (neg_mem
      (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp)))
      (sum_mem fun n _ => dg_mem_cpart D sy 𝒜 ?_)) (idg_mem_cpart D sy 𝒜 _ _)⟩
    rw [gsum_append, gsum_etaL, gsum_dcapL]; ring
  | invM₂ i ν _ =>
    exact ⟨0, add_mem (dg_mem_cpart D sy 𝒜 (by rw [gsum_append]; simp))
      (idg_mem_cpart D sy 𝒜 _ _)⟩
  | invM₃ i ν m _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | invM₄ i ν n _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | invM₅ i ν m n _ _ =>
    refine ⟨2 * sy.d i * (m - n), sub_mem (dg_mem_cpart D sy 𝒜 ?_) ?_⟩
    · rw [gsum_append, gsum_etaL, gsum_dcapL]; ring
    · split_ifs with hmn
      · subst hmn; rw [sub_self, mul_zero]; exact idg_mem_cpart D sy 𝒜 _ _
      · exact zero_mem _
  | dcupZero i ν n _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | dcapZero i ν n _ => exact ⟨_, dg_mem_cpart D sy 𝒜 rfl⟩
  | zInt b =>
    cases b with
    | sq i ν =>
      exact ⟨_, zGate_mem_part sy i fun _ => dg_mem_cpart D sy 𝒜 rfl⟩
    | right i ν n _ =>
      refine ⟨_, zGate_mem_part sy i fun _ => sub_mem (dg_mem_cpart D sy 𝒜 rfl)
        (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)⟩
      simp only [Rel.ν, ZBase.ν, gsum_append, gsum_etaL, gsum_rPostL, gsum_oddL]; push_cast; ring
    | left i ν n _ =>
      refine ⟨_, zGate_mem_part sy i fun _ => sub_mem (dg_mem_cpart D sy 𝒜 rfl)
        (smul_dg_mem_cpart D sy 𝒜 (zsign_mem_graded _) ?_)⟩
      simp only [Rel.ν, ZBase.ν, gsum_append, gsum_epsL, gsum_lPreL, gsum_oddL]; push_cast; ring

omit [SetLike.GradedMonoid 𝒜] in
/-- **Graded Hom groups of `𝔘(𝔤)`.** Under the graded parameter conditions, each Hom group is
the internal direct sum of its homogeneous parts for the coefficient grading. -/
theorem iSupIndep_coefficientGraded [GradedAlgebra 𝒜] {Ptwo : Prop} (Sc : ScalarData D k Ptwo)
    (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (coefficientDegree sy i j p q))
    (a b : Obj (sig D)) :
    iSupIndep (presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b) ∧
      ⨆ d, presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b d = ⊤ :=
  ⟨iSupIndep_presentedPart (isHomogeneous_coefficientGraded D sy 𝒜 Sc ht hs) a b,
    iSup_presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b⟩

end Relations

/-! ## Degrees of the decorated diagrams and bubbles -/

variable {Ptwo : Prop} {Sc : ScalarData D k Ptwo}

theorem cl_mem_presentedPart (μ : X) (s t : List (Letter I)) (L : List (LayerData I)) {d : ℤ}
    (hd : gsum D sy μ L = d) :
    cl D Sc μ s t L ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ s) (ob D μ t) d := by
  unfold cl
  split_ifs with h
  · exact diag_mem_presentedPart (by rw [degree_gdeg_mkD]; exact hd)
  · exact zero_mem _

variable (cs : CScalars Sc)

/-- The bubble normalizations `c_{λ;i}` and their inverses have degree `0`. -/
def CScalars.DegreeZero (𝒜 : ℤ → Submodule K k) : Prop :=
  ∀ μ i, ((cs.c μ i : kˣ) : k) ∈ 𝒜 0 ∧ ((↑(cs.c μ i)⁻¹ : kˣ) : k) ∈ 𝒜 0

variable {cs} (hc : cs.DegreeZero 𝒜)
include hc

theorem etaP_mem_presentedPart (i : I) (μ : X) :
    etaP cs i μ ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ (sy.d i * (1 - D.h i μ)) := by
  unfold etaP
  split_ifs with h
  · refine smul_mem_presentedPart_of_mem_zero (hc μ i).1 (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_dcupL, Int.toNat_of_nonneg (show 0 ≤ D.h i μ - 1 by omega)]
    ring
  · refine smul_mem_presentedPart_of_mem_zero
      (zsign_mul_mem_zero _ (hc μ i).1)
      (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_append, gsum_etaL, gsum_lcrossL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega)]
    ring

theorem epsP_mem_presentedPart (i : I) (μ : X) :
    epsP cs i μ ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ (sy.d i * (1 + D.h i μ)) := by
  unfold epsP
  split_ifs with h
  · refine smul_mem_presentedPart_of_mem_zero (hc μ i).2 (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_dcapL, Int.toNat_of_nonneg (show 0 ≤ -D.h i μ - 1 by omega)]
    ring
  · refine smul_mem_presentedPart_of_mem_zero
      (neg_mem (zsign_mul_mem_zero _ (hc μ i).2))
      (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_append, gsum_lcrossL, gsum_epsL,
      Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring

theorem bubL_mem_presentedPart (i : I) (μ : X) (n : ℤ) :
    bubL cs i μ n ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _
      (2 * sy.d i * (n - D.h i μ + 1)) := by
  unfold bubL
  split_ifs with hn hh he
  · have hd : sy.d i * (1 - D.h i μ) + gsum D sy μ (epsL i n.toNat) =
        2 * sy.d i * (n - D.h i μ + 1) := by
      rw [gsum_epsL, Int.toNat_of_nonneg hn]
      ring
    exact hd ▸ comp_mem_presentedPart (etaP_mem_presentedPart sy hc i μ)
      (cl_mem_presentedPart sy μ [up i, dn i] [] (epsL i n.toNat) rfl)
  · refine smul_mem_presentedPart_of_mem_zero
      (neg_zsign_mul_mem_zero _ (hc μ i).1)
      (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_append, gsum_etaL, gsum_dcapL,
      Int.toNat_of_nonneg (show 0 ≤ -D.h i μ by omega),
      Int.toNat_of_nonneg (show 0 ≤ -n - 1 by omega)]
    ring
  · rw [he, show 2 * sy.d i * (D.h i μ - 1 - D.h i μ + 1) = 0 by ring]
    exact smul_mem_presentedPart_of_mem_zero (hc μ i).1 (id_mem_presentedPart _)
  · exact zero_mem _

theorem bubR_mem_presentedPart (i : I) (μ : X) (n : ℤ) :
    bubR cs i μ n ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _
      (2 * sy.d i * (n + D.h i μ + 1)) := by
  unfold bubR
  split_ifs with hn hh he
  · have hd : gsum D sy μ (etaL i n.toNat) + sy.d i * (1 + D.h i μ) =
        2 * sy.d i * (n + D.h i μ + 1) := by
      rw [gsum_etaL, Int.toNat_of_nonneg hn]
      ring
    exact hd ▸ comp_mem_presentedPart
      (cl_mem_presentedPart sy μ [] [dn i, up i] (etaL i n.toNat) rfl)
      (epsP_mem_presentedPart sy hc i μ)
  · refine smul_mem_presentedPart_of_mem_zero
      (neg_zsign_mul_mem_zero _ (hc μ i).2)
      (cl_mem_presentedPart sy μ _ _ _ ?_)
    rw [gsum_append, gsum_dcupL, gsum_epsL,
      Int.toNat_of_nonneg (show 0 ≤ -n - 1 by omega),
      Int.toNat_of_nonneg (show 0 ≤ D.h i μ by omega)]
    ring
  · rw [he, show 2 * sy.d i * (-D.h i μ - 1 + D.h i μ + 1) = 0 by ring]
    exact smul_mem_presentedPart_of_mem_zero (hc μ i).2 (id_mem_presentedPart _)
  · exact zero_mem _

theorem bubLs_mem_presentedPart (i : I) (μ : X) (n : ℤ) :
    bubLs cs i μ n ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ (2 * sy.d i * n) := by
  simpa only [bubLs, show n + D.h i μ - 1 - D.h i μ + 1 = n by ring] using
    bubL_mem_presentedPart sy hc i μ (n + D.h i μ - 1)

theorem oddBubble_mem_presentedPart (i : I) (μ : X) :
    oddBubble cs i μ ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ (2 * sy.d i) := by
  unfold oddBubble
  split_ifs
  · refine smul_mem_presentedPart_of_mem_zero (hc μ i).2 ?_
    simpa only [sub_self, zero_add, mul_one] using bubL_mem_presentedPart sy hc i μ (D.h i μ)
  · refine smul_mem_presentedPart_of_mem_zero (hc μ i).1 ?_
    simpa only [neg_add_cancel, zero_add, mul_one] using
      bubR_mem_presentedPart sy hc i μ (-D.h i μ)

/-- Every coefficient generator has its degree `symGenDegree`. -/
theorem betaSYMGen_mem_presentedPart (μ : X) (g : SYMGen D) :
    betaSYMGen cs μ g ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D μ []) (ob D μ []) (symGenDegree D sy g) := by
  rcases g with ⟨i, n⟩ | i
  · dsimp only [betaSYMGen, symGenDegree]
    split_ifs
    · exact smul_mem_presentedPart_of_mem_zero (hc μ i).2 (bubLs_mem_presentedPart sy hc i μ _)
    · convert smul_mem_presentedPart_of_mem_zero (hc μ i).2
        (bubLs_mem_presentedPart sy hc i μ (2 * ((n : ℤ) + 1))) using 1 <;> try rfl
      congr 1
      ring
  · exact oddBubble_mem_presentedPart sy hc i μ

omit hc in
theorem plcL_mem_presentedPart {μ : X} {u v s t : List (Letter I)} {d : ℤ}
    {f : (pres D Sc).obj (ob D (wt D μ v) s) ⟶ (pres D Sc).obj (ob D (wt D μ v) t)}
    (hf : f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ d) :
    plcL D Sc μ u v s t f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D μ (u ++ s ++ v)) (ob D μ (u ++ t ++ v)) d := by
  unfold plcL
  split_ifs with h
  · dsimp only [plc, LinearMap.coe_mk, AddHom.coe_mk]
    simpa only [zero_add, add_zero] using comp_mem_presentedPart
      (eqToHom_mem_presentedPart (𝒜 := 𝒜) (deg := gdeg D sy)
        (congrArg (pres D Sc).obj (ob_whisker D μ u v s s rfl).symm))
      (comp_mem_presentedPart (whisk_mem_presentedPart hf _ _)
        (eqToHom_mem_presentedPart (𝒜 := 𝒜) (deg := gdeg D sy)
          (congrArg (pres D Sc).obj (ob_whisker D μ u v s t h))))
  · exact zero_mem _

omit hc [SetLike.GradedMonoid 𝒜] in
theorem wordCast_mem_presentedPart {μ : X} {s t s' t' : List (Letter I)}
    (hs : s = s') (ht : t = t') {d : ℤ}
    {f : (pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)}
    (hf : f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ d) :
    wordCast μ hs ht f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ s') (ob D μ t') d := by
  subst s' t'
  exact hf

omit hc in
theorem bubAt_mem_presentedPart {μ : X} (v : List (Letter I)) {d : ℤ}
    {f : (pres D Sc).obj (ob D μ []) ⟶ (pres D Sc).obj (ob D μ [])}
    (hf : f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) _ _ d) :
    bubAt D Sc μ v f ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ v) (ob D μ v) d :=
  wordCast_mem_presentedPart sy _ _ (plcL_mem_presentedPart sy hf)

theorem xlay_mem_presentedPart (μ : X) (x : XLayer I) :
    xlay cs μ x ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D μ (x.1 ++ x.2.1.dom ++ x.2.2))
      (ob D μ (x.1 ++ x.2.1.cod ++ x.2.2)) (tableDegree D sy μ [x]) := by
  rcases x with ⟨a, g, b⟩
  cases g <;>
    simp only [xlay, XShape.dom, XShape.cod, tableDegree, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, add_zero]
  · rename_i g
    exact cl_mem_presentedPart sy μ (a ++ g.dom ++ b) (a ++ g.cod ++ b) [(a, g, b)]
      (by simp only [gsum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero])
  · exact plcL_mem_presentedPart sy (μ := μ) (u := a) (v := b)
      (etaP_mem_presentedPart sy hc _ (wt D μ b))
  · exact plcL_mem_presentedPart sy (μ := μ) (u := a) (v := b)
      (epsP_mem_presentedPart sy hc _ (wt D μ b))

/-- Evaluation of an extended diagram has the degree of its table sum. -/
theorem xev_mem_presentedPart (μ : X) (s t : List (Letter I)) (L : List (XLayer I)) :
    xev cs μ s t L ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D μ s) (ob D μ t) (tableDegree D sy μ L) := by
  induction L generalizing s with
  | nil => exact cl_mem_presentedPart sy μ s t [] rfl
  | cons x L ih =>
    simpa only [xev_cons, tableDegree, gsum, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, add_zero, zero_add] using
      comp_mem_presentedPart (cl_mem_presentedPart sy μ s _ [] rfl)
        (comp_mem_presentedPart (xlay_mem_presentedPart sy hc μ x) (ih _))

/-! ## Degrees of coefficient monomials -/

omit hc

variable (𝒜 Sc) in
/-- The degree-`n` part of the endomorphisms of the empty word. -/
abbrev endPart (μ : X) (n : ℤ) : AddSubgroup (End ((pres D Sc).obj (ob D μ []))) :=
  presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ []) (ob D μ []) n

instance endPart_gradedMonoid (μ : X) : SetLike.GradedMonoid (endPart sy 𝒜 Sc μ) where
  one_mem := id_mem_presentedPart (𝒜 := 𝒜) (deg := gdeg D sy) (P := pres D Sc) (ob D μ [])
  mul_mem i j x y hx hy := by
    rw [End.mul_def, add_comm]
    exact comp_mem_presentedPart hy hx

/-- Pullback of `endPart` along a ring homomorphism. -/
def endPartComap {R : Type*} [Ring R] (μ : X)
    (φ : R →+* End ((pres D Sc).obj (ob D μ []))) (n : ℤ) : AddSubgroup R :=
  (endPart sy 𝒜 Sc μ n).comap φ.toAddMonoidHom

instance endPartComap_gradedMonoid {R : Type*} [Ring R] (μ : X)
    (φ : R →+* End ((pres D Sc).obj (ob D μ []))) :
    SetLike.GradedMonoid (endPartComap sy (𝒜 := 𝒜) μ φ) where
  one_mem := by
    show φ.toAddMonoidHom 1 ∈ endPart sy 𝒜 Sc μ 0
    rw [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, map_one]
    exact SetLike.GradedOne.one_mem
  mul_mem i j x y hx hy := by
    have hx' : φ x ∈ endPart sy 𝒜 Sc μ i := hx
    have hy' : φ y ∈ endPart sy 𝒜 Sc μ j := hy
    show φ.toAddMonoidHom (x * y) ∈ endPart sy 𝒜 Sc μ (i + j)
    simpa using SetLike.GradedMul.mul_mem hx' hy'

theorem symGenDegree_inl (x : I × ℕ) :
    symGenDegree D sy (.inl x) = 2 * sy.d x.1 * (SYM.elementaryWeight D x : ℤ) := by
  rcases x with ⟨i, n⟩
  simp only [symGenDegree, SYM.elementaryWeight]
  split_ifs <;> push_cast <;> ring

theorem sum_oddOrdered (s : Finset {i : I // D.parity i = 1})
    (f : {i : I // D.parity i = 1} → ℤ) :
    ∑ j : Fin s.card, f (SYM.oddOrdered D s j) = ∑ i ∈ s, f i := by
  let _ : LinearOrder {i : I // D.parity i = 1} := WellOrderingRel.isWellOrder.linearOrder
  calc ∑ j : Fin s.card, f (SYM.oddOrdered D s j)
      = ∑ j : Fin s.card, (fun x : s => f x) ((s.orderIsoOfFin rfl).toEquiv j) := rfl
    _ = ∑ x : s, f x := Equiv.sum_comp _ (fun x : s => f x)
    _ = ∑ i ∈ s, f i := Finset.sum_coe_sort s f

include hc

/-- **Homogeneous coefficient monomials.** The bubble image of a coefficient basis vector has
its coefficient degree. -/
theorem betaSYM_coefficientBasis_mem (μ : X) (a : SYM.CoefficientIndex D) :
    betaSYM cs μ (SYM.coefficientBasis D k a) ∈ endPart sy 𝒜 Sc μ (SYM.coefficientDegree D sy a) := by
  rw [SYM.coefficientBasis_eq_prod, map_mul, SYM.coefficientDegree]
  refine SetLike.GradedMul.mul_mem ?_ ?_
  · let φ : MvPolynomial (I × ℕ) k →+* End ((pres D Sc).obj (ob D μ [])) :=
      (betaSYM cs μ).toRingHom.comp (SYM.polynomialPart D k).toRingHom
    have hm : MvPolynomial.monomial a.1 (1 : k) ∈ endPartComap sy (𝒜 := 𝒜) μ φ
        (a.1.sum fun x n => (n : ℤ) * (2 * sy.d x.1 * SYM.elementaryWeight D x)) := by
      rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod, Finsupp.sum]
      refine SetLike.prod_mem_graded _ _ _ fun x _ => ?_
      have h := betaSYMGen_mem_presentedPart sy hc μ (.inl x)
      rw [← betaSYM_ι, symGenDegree_inl] at h
      have h' : MvPolynomial.X x ∈ endPartComap sy (𝒜 := 𝒜) μ φ
          (2 * sy.d x.1 * (SYM.elementaryWeight D x : ℤ)) := by
        show betaSYM cs μ (SYM.polynomialPart D k (MvPolynomial.X x)) ∈ endPart sy 𝒜 Sc μ _
        rw [SYM.polynomialPart_X]
        exact h
      convert SetLike.pow_mem_graded (a.1 x) h' using 2
    exact hm
  · rw [map_list_prod, List.map_ofFn, ← sum_oddOrdered]
    have := SetLike.list_prod_ofFn_mem_graded (A := endPart sy 𝒜 Sc μ)
      (fun j => 2 * sy.d (SYM.oddOrdered D a.2 j).1)
      (betaSYM cs μ ∘ fun j => SYM.delta D k (SYM.oddOrdered D a.2 j))
      (fun j => by
        rw [Function.comp_apply, betaSYM_delta]
        exact betaSYMGen_mem_presentedPart sy hc μ (.inr _))
    rwa [List.sum_ofFn] at this

variable (μ : X) {a b : List (Letter I)}

/-- **Homogeneous basis elements.** The decorated matching `F_t` times `r b_a`, for a
coefficient monomial `b_a` and `r ∈ 𝒜 e`, has degree `e + deg b_a + deg F_t` for the total
coefficient grading. -/
theorem expansion_single_smul_coefficientBasis_mem (F : MatchingBasisChoice a b)
    (t : F.Labels) (c : SYM.CoefficientIndex D) {r : k} {e : ℤ} (hr : r ∈ 𝒜 e) :
    F.expansion cs μ (Finsupp.single t (r • SYM.coefficientBasis D k c)) ∈
      presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ a) (ob D μ b)
        (e + SYM.coefficientDegree D sy c + tableDegree D sy μ (F.layers t)) := by
  rw [← Finsupp.smul_single, map_smul, F.expansion_single, add_assoc]
  exact smul_mem_presentedPart_of_mem hr (comp_mem_presentedPart
    (bubAt_mem_presentedPart sy a (betaSYM_coefficientBasis_mem sy hc μ c))
    (xev_mem_presentedPart sy hc μ a b (F.layers t)))

theorem expansion_single_coefficientBasis_mem (F : MatchingBasisChoice a b)
    (t : F.Labels) (c : SYM.CoefficientIndex D) :
    F.expansion cs μ (Finsupp.single t (SYM.coefficientBasis D k c)) ∈
      presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ a) (ob D μ b)
        (SYM.coefficientDegree D sy c + tableDegree D sy μ (F.layers t)) := by
  simpa using expansion_single_smul_coefficientBasis_mem sy hc μ F t c
    (SetLike.GradedOne.one_mem (A := 𝒜))

omit hc in
variable (cs) in
/-- Under `IsBasis`, the elements `F_t b_a` form a `k`-basis of the Hom group. -/
def MatchingBasisChoice.homogeneousBasis (F : MatchingBasisChoice a b) (hF : F.IsBasis cs μ) :
    Module.Basis ((_ : F.Labels) × SYM.CoefficientIndex D) k
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  (Finsupp.basis fun _ => SYM.coefficientBasis D k).map
    (LinearEquiv.ofBijective (F.expansion cs μ) hF)

omit hc in
theorem MatchingBasisChoice.homogeneousBasis_apply (F : MatchingBasisChoice a b)
    (hF : F.IsBasis cs μ) (x : (_ : F.Labels) × SYM.CoefficientIndex D) :
    F.homogeneousBasis cs μ hF x =
      F.expansion cs μ (Finsupp.single x.1 (SYM.coefficientBasis D k x.2)) := by
  simp [MatchingBasisChoice.homogeneousBasis]

/-- **Homogeneous bases for the total coefficient grading.** Each element `F_t b_a` of the
basis has degree `deg b_a + deg F_t`. -/
theorem MatchingBasisChoice.homogeneousBasis_mem (F : MatchingBasisChoice a b)
    (hF : F.IsBasis cs μ) (x : (_ : F.Labels) × SYM.CoefficientIndex D) :
    F.homogeneousBasis cs μ hF x ∈ presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D μ a) (ob D μ b)
      (SYM.coefficientDegree D sy x.2 + tableDegree D sy μ (F.layers x.1)) := by
  rw [F.homogeneousBasis_apply μ hF x]
  exact expansion_single_coefficientBasis_mem sy hc μ F x.1 x.2

end OddMath.SKM

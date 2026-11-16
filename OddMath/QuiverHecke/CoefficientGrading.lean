/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Grading
import OddMath.SKM.GradedParameters
import OddMath.Diagrams.CoefficientGradedSupercategory

/-!
# The quiver Hecke presentation with graded parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5,
the parameters (1.6) and the degree table after (1.31); J. Brundan, W. Wang, B. Webster,
arXiv:2505.22929v2, §2.2 (parameters over a graded ring).

`isHomogeneous_gdeg` grades the quiver Hecke presentation when every scalar has degree zero,
which forces (1.31). Here the ground ring `k` is graded by `𝒜 : ℤ → Submodule K k`. If the
units `tᵢⱼ` have degree `0` and each nonzero `sᵢⱼ^{pq}` has its coefficient degree
`2(dᵢdᵢⱼ - dᵢp - dⱼq)`, then every defining relation lies in one degree for the coefficient
grading of `OddMath.Diagrams.CoefficientGrading`, with the same generator degrees `gdeg`.
The Rees parameters `sᵢⱼ^{pq} h^{deg}` of a lower-degree parameter system satisfy this over
`K[h]` and its truncations, with `h` in degree `1` (route step 2 of
`docs/Nondegeneracy/Phase2Plan.md`, item 3).

## Main results

* `QuiverHecke.isHomogeneous_coefficientGraded`: the quiver Hecke presentation is
  coefficient-graded homogeneous.
* `QuiverHecke.isHomogeneous_rees`: the case of the Rees parameters of a lower-degree
  parameter system over `K[h]`.
* `QuiverHecke.iSupIndep_coefficientGraded`: hence each Hom group of `H D Sc` is the internal
  direct sum of its homogeneous parts.
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams LinDiagram OddMath.Diagrams
open SKM (zsign dn_cast')

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {K : Type*} [CommRing K] {k : Type w} [CommRing k] [Algebra K k]
  (sy : SKM.Symmetrizer D) (𝒜 : ℤ → Submodule K k) [SetLike.GradedMonoid 𝒜]

/-- A normal-form diagram of degree `d` lies in the degree-`d` part. -/
theorem dg_mem_part {t t' : List I} {ls : List (LayerData I)} {h : SChain t ls t'} {d : ℤ}
    (hd : gsum D sy ls = d) :
    dg (k := k) D ls h ∈ CoefficientGrading.part 𝒜 (gdeg D sy) (ob D t) (ob D t') d :=
  CoefficientGrading.of_mem_part' _ (by rw [degree_gdeg_mkD]; exact hd)

theorem idg_mem_part (t : List I) :
    idg (k := k) D t ∈ CoefficientGrading.part 𝒜 (gdeg D sy) (ob D t) (ob D t) 0 :=
  CoefficientGrading.of_mem_part' _ (Diagram.degree_id _ _)

/-- A coefficient of degree `m` times a normal-form diagram. -/
theorem smul_dg_mem_part {t t' : List I} {ls : List (LayerData I)} {h : SChain t ls t'}
    {r : k} {m d : ℤ} (hr : r ∈ 𝒜 m) (hd : m + gsum D sy ls = d) :
    r • dg (k := k) D ls h ∈ CoefficientGrading.part 𝒜 (gdeg D sy) (ob D t) (ob D t') d :=
  by subst hd; exact CoefficientGrading.smul_mem_part hr (dg_mem_part D sy 𝒜 rfl)

variable {𝒜} in
theorem zsign_mem (p : ZMod 2) : zsign k p ∈ 𝒜 0 := by
  unfold zsign
  split_ifs
  · exact neg_mem SetLike.GradedOne.one_mem
  · exact SetLike.GradedOne.one_mem

/-- **Graded parameters.** If the `tᵢⱼ` have degree `0` and every nonzero `sᵢⱼ^{pq}` has its
coefficient degree, every defining relation of the quiver Hecke presentation lies in one
degree for the coefficient grading. -/
theorem isHomogeneous_coefficientGraded (Sc : SKM.Scalars D k)
    (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q)) :
    CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc) := by
  intro r
  cases r with
  | quadEq i =>
    exact ⟨_, dg_mem_part D sy 𝒜 rfl⟩
  | quadZero i j _ hd =>
    refine ⟨0, sub_mem (dg_mem_part D sy 𝒜 ?_)
      (CoefficientGrading.smul_mem_part_zero (ht i j) (idg_mem_part D sy 𝒜 _))⟩
    rw [gsum_append, gsum_crossL, gsum_crossL, hd, (D.d_eq_zero_iff i j).mp hd]; ring
  | quadNe i j hij hd =>
    refine ⟨2 * (sy.d i * D.d i j), sub_mem (sub_mem (sub_mem (dg_mem_part D sy 𝒜 ?_)
      (smul_dg_mem_part D sy 𝒜 (ht i j) ?_)) (smul_dg_mem_part D sy 𝒜 (ht j i) ?_))
      (sum_mem fun p hp => sum_mem fun q hq => ?_)⟩
    · rw [gsum_append, gsum_crossL, gsum_crossL]; have := sy.symm i j; linarith
    · rw [gsum_dotsL, dn_cast' hij]; ring
    · rw [gsum_dotsL, dn_cast' (Ne.symm hij)]; have := sy.symm i j; linarith
    · by_cases h0 : Sc.s i j p q = 0
      · rw [h0, zero_smul]; exact zero_mem _
      · rw [Finset.mem_range] at hp hq
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq
        refine smul_dg_mem_part D sy 𝒜 (hs i j p q hij hp' hq' h0) ?_
        rw [gsum_append, gsum_dotsL, gsum_dotsL, SKM.coefficientDegree]; ring
  | slideL i j _ =>
    refine ⟨2 * sy.d i + sy.d i * D.d i j, sub_mem (dg_mem_part D sy 𝒜 ?_)
      (smul_dg_mem_part D sy 𝒜 (zsign_mem _) ?_)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideLEq i =>
    refine ⟨0, sub_mem (sub_mem (dg_mem_part D sy 𝒜 ?_)
      (smul_dg_mem_part D sy 𝒜 (zsign_mem _) ?_)) (idg_mem_part D sy 𝒜 _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | slideR i j _ =>
    refine ⟨2 * sy.d j + sy.d i * D.d i j, sub_mem (dg_mem_part D sy 𝒜 ?_)
      (smul_dg_mem_part D sy 𝒜 (zsign_mem _) ?_)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideREq i =>
    refine ⟨0, sub_mem (sub_mem (dg_mem_part D sy 𝒜 ?_)
      (smul_dg_mem_part D sy 𝒜 (zsign_mem _) ?_)) (idg_mem_part D sy 𝒜 _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | braid i j k' _ =>
    refine ⟨sy.d i * D.d i j + sy.d i * D.d i k' + sy.d j * D.d j k',
      sub_mem (dg_mem_part D sy 𝒜 ?_) (dg_mem_part D sy 𝒜 ?_)⟩
    all_goals (simp only [gsum_append, gsum_crossL]; try ring)
  | braidEq i j hij =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j) - 2 * sy.d i, sub_mem (sub_mem
      (sub_mem (dg_mem_part D sy 𝒜 ?_) (dg_mem_part D sy 𝒜 ?_))
      (sum_mem fun s hs' => smul_dg_mem_part D sy 𝒜
        (by
          have := SetLike.GradedMul.mul_mem (zsign_mem (𝒜 := 𝒜) (D.parity i * (D.parity j + s)))
            (ht i j)
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
        refine smul_dg_mem_part D sy 𝒜
          (SetLike.GradedMul.mul_mem (zsign_mem _) (hs i j p q hij hp' hq' hz)) ?_
        rw [gsum_append, gsum_append, gsum_dotsL, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega),
          Nat.cast_sub (by omega), SKM.coefficientDegree]
        push_cast; ring

omit [SetLike.GradedMonoid 𝒜] in
/-- **Graded Hom groups.** Under the graded parameter conditions, each Hom group of the quiver
Hecke supercategory is the internal direct sum of its homogeneous parts for the coefficient
grading. -/
theorem iSupIndep_coefficientGraded [GradedAlgebra 𝒜] (Sc : SKM.Scalars D k)
    (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
    (hs : ∀ i j (p q : ℕ), i ≠ j → (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
      Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
    (a b : Obj (sig D)) :
    iSupIndep (CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b) ∧
      ⨆ d, CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b d = ⊤ :=
  ⟨CoefficientGrading.iSupIndep_presentedPart
      (isHomogeneous_coefficientGraded D sy 𝒜 Sc ht hs) a b,
    CoefficientGrading.iSup_presentedPart 𝒜 (gdeg D sy) (pres D Sc) a b⟩

/-! ## Rees parameters -/

section Rees

open MvPolynomial

attribute [local instance] MvPolynomial.WeightedHomogeneousSubmodule.gradedMonoid

/-- The grading of `K[h] = MvPolynomial Unit K` with `h` in degree `1`, indexed by `ℤ`. -/
abbrev reesGrading (K : Type*) [CommRing K] : ℤ → Submodule K (MvPolynomial Unit K) :=
  weightedHomogeneousSubmodule K (fun _ : Unit => (1 : ℤ))

theorem C_mul_X_pow_mem_reesGrading (a : K) (n : ℕ) {d : ℤ} (hd : (n : ℤ) = d) :
    C a * MvPolynomial.X () ^ n ∈ reesGrading K d := by
  rw [mem_weightedHomogeneousSubmodule]
  have := (isWeightedHomogeneous_C (fun _ : Unit => (1 : ℤ)) a).mul
    ((isWeightedHomogeneous_X K (fun _ : Unit => (1 : ℤ)) ()).pow n)
  simpa [← hd] using this

theorem C_mem_reesGrading (a : K) : (C a : MvPolynomial Unit K) ∈ reesGrading K 0 := by
  rw [mem_weightedHomogeneousSubmodule]
  exact isWeightedHomogeneous_C _ a

theorem rees_t_mem (Sc : SKM.Scalars D K) (i j : I) :
    (((SKM.ReesParameters.scalars sy Sc).t i j : (MvPolynomial Unit K)ˣ) : MvPolynomial Unit K) ∈
      reesGrading K 0 :=
  C_mem_reesGrading ((Sc.t i j : Kˣ) : K)

theorem rees_s_mem {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) (i j : I) (p q : ℕ)
    (hij : i ≠ j) (hp' : (p : ℤ) < D.d i j) (hq' : (q : ℤ) < D.d j i)
    (hs : (SKM.ReesParameters.scalars sy Sc).s i j p q ≠ 0) :
    (SKM.ReesParameters.scalars sy Sc).s i j p q ∈
      reesGrading K (SKM.coefficientDegree sy i j p q) := by
  have hs' : Sc.s i j p q ≠ 0 := by
    intro h0
    apply hs
    change C (Sc.s i j p q) * MvPolynomial.X () ^ _ = 0
    rw [h0, map_zero, zero_mul]
  exact C_mul_X_pow_mem_reesGrading _ _ (Int.toNat_of_nonneg (hl i j p q hij hp' hq' hs'))

/-- **Rees parameters.** For lower-degree parameters over `K`, the quiver Hecke presentation
with the Rees parameters `sᵢⱼ^{pq} h^{deg}` over `K[h]` is coefficient-graded homogeneous for
`h` in degree `1`. -/
theorem isHomogeneous_rees {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) :
    CoefficientGrading.IsHomogeneous (reesGrading K) (gdeg D sy)
      (pres D (SKM.ReesParameters.scalars sy Sc)) :=
  isHomogeneous_coefficientGraded D sy (reesGrading K) _ (rees_t_mem D sy Sc)
    (rees_s_mem D sy hl)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- **Graded quiver Hecke supercategory over `K[h]`.** For lower-degree parameters over `K`,
the quiver Hecke supercategory with the Rees parameters over `K[h]`, viewed as `K`-linear, is
a graded supercategory with `h` in degree `1`. -/
@[instance_reducible]
def reesGradedSupercategory {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) :
    letI := Diagrams.Linear.restrictScalars K (MvPolynomial Unit K)
      (H D (SKM.ReesParameters.scalars sy Sc))
    letI := Diagrams.Supercategory.restrictScalars K (MvPolynomial Unit K)
      (H D (SKM.ReesParameters.scalars sy Sc))
    GradedSupercategory K (H D (SKM.ReesParameters.scalars sy Sc)) :=
  CoefficientGrading.gradedSupercategory (isParityHomogeneous D _) (isHomogeneous_rees D sy hl)

end Rees

end OddMath.QuiverHecke

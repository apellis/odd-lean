/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Presentation

/-!
# The grading of `𝔘(𝔤)` (Brundan–Ellis, (1.31) and the degree table)

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, paragraph
"Gradings": assume the Cartan matrix is symmetrized by positive integers `dᵢ`
(`dᵢ dᵢⱼ = dⱼ dⱼᵢ`; `Symmetrizer`) and the parameters satisfy the homogeneity condition (1.31)
`sᵢⱼ^{pq} ≠ 0 → p dⱼᵢ + q dᵢⱼ = dᵢⱼ dⱼᵢ` (`Scalars.Homogeneous`). Then the generators have the
degrees of the table after (1.31) (`gdeg`):

| `x` | `τ` | `η` | `ε` |
|---|---|---|---|
| `2dᵢ` | `dᵢ dᵢⱼ` | `dᵢ(1 + ⟨hᵢ, λ⟩)` | `dᵢ(1 - ⟨hᵢ, λ⟩)` |

where `λ` is the weight of the rightmost region of the generator. The paper also lists the
degrees of `η'`, `ε'`, which are defined in §2 from the inverse entries; the degrees of the
inverse entries are forced by the inversion relations: the leftward crossing has degree `0`
(as `σ` does), the `♦`-cup with label `n` has degree `dᵢ(⟨hᵢ, λ⟩ - 1 - 2n)` (inverse to
`ε ∘ (xⁿ ⊗ 1)`), and the `♦`-cap with label `n` has degree `-dᵢ(⟨hᵢ, λ⟩ + 1 + 2n)` (inverse to
`(1 ⊗ xⁿ) ∘ η`). With these degrees every relation of Definition 1.5 is homogeneous
(`isHomogeneous_gdeg`); this is the statement "we can put an additional `ℤ`-grading on `𝔘(𝔤)`
making it into a graded 2-supercategory". The paper assumes in addition that `k` is a field;
that is not needed for the grading.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams LinDiagram

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X)

/-- A symmetrization of the Cartan matrix: positive integers `dᵢ` with `dᵢ dᵢⱼ = dⱼ dⱼᵢ`. -/
structure Symmetrizer where
  /-- The integers `dᵢ`. -/
  d : I → ℤ
  pos : ∀ i, 0 < d i
  symm : ∀ i j, d i * D.d i j = d j * D.d j i

variable {k : Type w} [CommRing k] {D}

/-- The homogeneity condition (1.31): `sᵢⱼ^{pq} ≠ 0 → p dⱼᵢ + q dᵢⱼ = dᵢⱼ dⱼᵢ`, for
`0 < p < dᵢⱼ`, `0 < q < dⱼᵢ` (the range in which the scalars are used). -/
def Scalars.Homogeneous (Sc : Scalars D k) : Prop :=
  ∀ i j (p q : ℕ), 0 < p → (p : ℤ) < D.d i j → 0 < q → (q : ℤ) < D.d j i → Sc.s i j p q ≠ 0 →
    p * D.d j i + q * D.d i j = D.d i j * D.d j i

variable (D) (sy : Symmetrizer D)

/-- The degrees of the generators (table after (1.31), and the forced degrees of the inverse
entries; see the module docstring). The second component is the weight of the rightmost
region. -/
def gdeg : (sig D).Gen → ℤ
  | (.dot i, _) => 2 * sy.d i
  | (.cross i j, _) => sy.d i * D.d i j
  | (.cup i, ν) => sy.d i * (1 + D.h i ν)
  | (.cap i, ν) => sy.d i * (1 - D.h i ν)
  | (.lcross _ _, _) => 0
  | (.dcup i n, ν) => sy.d i * (D.h i ν - 1 - 2 * n)
  | (.dcap i n, ν) => -(sy.d i * (D.h i ν + 1 + 2 * n))

/-- The degree of a normal-form diagram: the sum of the degrees of its generators, each in the
region `wt μ v` to its right. -/
theorem degree_gdeg_mkD (μ : X) {t t' : List (Letter I)} (ls : List (LayerData I))
    (h : SChain t ls t') :
    Diagram.degree (gdeg D sy) (mkD D μ ls h) =
      (ls.map fun x => gdeg D sy (x.2.1, wt D μ x.2.2)).sum := by
  simp only [Diagram.degree, layers_mkD, layList, List.map_map]
  rfl

/-- The degree of a layer list (for the homogeneity proofs). -/
abbrev gsum (μ : X) (ls : List (LayerData I)) : ℤ :=
  (ls.map fun x => gdeg D sy (x.2.1, wt D μ x.2.2)).sum

theorem gsum_append (μ : X) (ls ms : List (LayerData I)) :
    gsum D sy μ (ls ++ ms) = gsum D sy μ ls + gsum D sy μ ms := by
  simp [gsum]

@[simp] theorem h_sh_up (i j : I) : D.h i (sh D (true, j)) = -D.d i j := by
  simp [sh, Datum.d]

@[simp] theorem h_sh_dn (i j : I) : D.h i (sh D (false, j)) = D.d i j := by
  simp [sh, Datum.d]

@[simp] theorem gsum_dotsL (μ : X) (u : List (Letter I)) (i : I) (v : List (Letter I)) (n : ℕ) :
    gsum D sy μ (dotsL u i v n) = n * (2 * sy.d i) := by
  simp [gsum, dotsL, gdeg, List.sum_replicate]

@[simp] theorem gsum_crossL (μ : X) (u : List (Letter I)) (i j : I) (v : List (Letter I)) :
    gsum D sy μ (crossL u i j v) = sy.d i * D.d i j := by
  simp [gsum, crossL, gdeg]

@[simp] theorem gsum_lcrossL (μ : X) (i j : I) : gsum D sy μ (lcrossL i j) = 0 := by
  simp [gsum, lcrossL, gdeg]

@[simp] theorem gsum_sigmaL (μ : X) (i j : I) : gsum D sy μ (sigmaL i j) = 0 := by
  simp [gsum, sigmaL, gdeg, Datum.d_self]
  ring

@[simp] theorem gsum_epsL (μ : X) (i : I) (n : ℕ) :
    gsum D sy μ (epsL i n) = n * (2 * sy.d i) + sy.d i * (1 - D.h i μ) := by
  rw [epsL, gsum_append, gsum_dotsL]; simp [gsum, gdeg]

@[simp] theorem gsum_etaL (μ : X) (i : I) (n : ℕ) :
    gsum D sy μ (etaL i n) = sy.d i * (1 + D.h i μ) + n * (2 * sy.d i) := by
  rw [etaL, gsum_append, gsum_dotsL]; simp [gsum, gdeg]

@[simp] theorem gsum_dcupL (μ : X) (i : I) (n : ℕ) :
    gsum D sy μ (dcupL i n) = sy.d i * (D.h i μ - 1 - 2 * n) := by
  simp [gsum, dcupL, gdeg]

@[simp] theorem gsum_dcapL (μ : X) (i : I) (n : ℕ) :
    gsum D sy μ (dcapL i n) = -(sy.d i * (D.h i μ + 1 + 2 * n)) := by
  simp [gsum, dcapL, gdeg]

/-- A normal-form diagram of degree `d` lies in the degree-`d` part. -/
theorem dg_mem_gdeg {μ : X} {t t' : List (Letter I)} {ls : List (LayerData I)}
    {h : SChain t ls t'} {d : ℤ} (hd : gsum D sy μ ls = d) :
    dg (k := k) D μ ls h ∈ LinDiagram.homDeg k (gdeg D sy) (ob D μ t) (ob D μ t') d :=
  of_mem_homDeg' (by rw [degree_gdeg_mkD]; exact hd)

theorem idg_mem_gdeg (μ : X) (t : List (Letter I)) :
    idg (k := k) D μ t ∈ LinDiagram.homDeg k (gdeg D sy) (ob D μ t) (ob D μ t) 0 :=
  of_mem_homDeg' (Diagram.degree_id _ _)

variable {D sy}

theorem dn_cast' {i j : I} (hij : i ≠ j) : ((D.dn i j : ℕ) : ℤ) = D.d i j := D.dn_cast hij

variable (D sy)

/-- **The grading of `𝔘(𝔤)`** (Brundan–Ellis, §1, "Gradings"): under the homogeneity condition
(1.31), every relation of Definition 1.5 is homogeneous for the degrees `gdeg`. -/
theorem isHomogeneous_gdeg (Sc : Scalars D k) (hc : Sc.Homogeneous) :
    (pres D Sc).IsHomogeneous (gdeg D sy) := by
  intro r
  cases r with
  | quadEq i ν =>
    exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | quadZero i j ν _ hd =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (idg_mem_gdeg D sy _ _))⟩
    rw [gsum_append, gsum_crossL, gsum_crossL, hd, (D.d_eq_zero_iff i j).mp hd]; ring
  | quadNe i j ν hij hd =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j), Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq => ?_)⟩
    · rw [gsum_append, gsum_crossL, gsum_crossL]; linarith
    · rw [gsum_dotsL, dn_cast' hij]; ring
    · rw [gsum_dotsL, dn_cast' (Ne.symm hij)]; linarith
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)
        rw [Finset.mem_Ioo] at hp hq
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp.2
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq.2
        have h31 := hc i j p q hp.1 hp' hq.1 hq' hs
        have hdji : D.d j i ≠ 0 := fun h0 => hd ((D.d_eq_zero_iff i j).mpr h0)
        rw [gsum_append, gsum_dotsL, gsum_dotsL]
        have key : D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j) = 0 := by
          have e1 : D.d j i * (sy.d j * q) = q * (sy.d i * D.d i j) := by rw [hji]; ring
          calc D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j)
              = sy.d i * (p * D.d j i - D.d i j * D.d j i) + D.d j i * (sy.d j * q) := by ring
            _ = sy.d i * (p * D.d j i - D.d i j * D.d j i) + q * (sy.d i * D.d i j) := by rw [e1]
            _ = sy.d i * (p * D.d j i + q * D.d i j - D.d i j * D.d j i) := by ring
            _ = 0 := by rw [h31]; ring
        have := (mul_eq_zero.mp key).resolve_left hdji
        linarith
  | slideL i j ν _ =>
    refine ⟨2 * sy.d i + sy.d i * D.d i j, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideLEq i ν =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))) (idg_mem_gdeg D sy _ _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | slideR i j ν _ =>
    refine ⟨2 * sy.d j + sy.d i * D.d i j, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL]; ring
  | slideREq i ν =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_)
      (Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_))) (idg_mem_gdeg D sy _ _)⟩
    all_goals rw [gsum_append]; simp only [gsum_dotsL, gsum_crossL, D.d_self]; ring
  | braid i j k' ν _ =>
    refine ⟨sy.d i * D.d i j + sy.d i * D.d i k' + sy.d j * D.d j k',
      Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (dg_mem_gdeg D sy ?_)⟩
    all_goals (simp only [gsum_append, gsum_crossL]; try ring)
  | braidEq i j ν hij =>
    have hji := sy.symm i j
    refine ⟨2 * (sy.d i * D.d i j) - 2 * sy.d i, Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (dg_mem_gdeg D sy ?_))
      (Submodule.sum_mem _ fun s hs => Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)))
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq =>
        Submodule.sum_mem _ fun s hs => ?_)⟩
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · simp only [gsum_append, gsum_crossL, D.d_self]; linarith
    · rw [Finset.mem_range] at hs
      rw [gsum_append, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega), Nat.cast_sub (by omega),
        dn_cast' hij]
      push_cast; ring
    · by_cases hz : Sc.s i j p q = 0
      · rw [hz, mul_zero, zero_smul]; exact Submodule.zero_mem _
      · refine Submodule.smul_mem _ _ (dg_mem_gdeg D sy ?_)
        rw [Finset.mem_Ioo] at hp hq
        rw [Finset.mem_range] at hs
        have hp' : (p : ℤ) < D.d i j := by rw [← dn_cast' hij]; exact_mod_cast hp.2
        have hq' : (q : ℤ) < D.d j i := by rw [← dn_cast' (Ne.symm hij)]; exact_mod_cast hq.2
        have h31 := hc i j p q hp.1 hp' hq.1 hq' hz
        have hd : D.d i j ≠ 0 := by omega
        have hdji : D.d j i ≠ 0 := fun h0 => hd ((D.d_eq_zero_iff i j).mpr h0)
        have key : D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j) = 0 := by
          have e1 : D.d j i * (sy.d j * q) = q * (sy.d i * D.d i j) := by rw [hji]; ring
          calc D.d j i * (sy.d i * p + sy.d j * q - sy.d i * D.d i j)
              = sy.d i * (p * D.d j i - D.d i j * D.d j i) + D.d j i * (sy.d j * q) := by ring
            _ = sy.d i * (p * D.d j i - D.d i j * D.d j i) + q * (sy.d i * D.d i j) := by rw [e1]
            _ = sy.d i * (p * D.d j i + q * D.d i j - D.d i j * D.d j i) := by ring
            _ = 0 := by rw [h31]; ring
        have := (mul_eq_zero.mp key).resolve_left hdji
        rw [gsum_append, gsum_append, gsum_dotsL, gsum_dotsL, gsum_dotsL, Nat.cast_sub (by omega),
          Nat.cast_sub (by omega)]
        push_cast; linarith
  | zigE i ν =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (idg_mem_gdeg D sy _ _)⟩
    simp [gsum, gdeg, Datum.d_self]; ring
  | zigF i ν =>
    refine ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) (idg_mem_gdeg D sy _ _)⟩
    simp [gsum, gdeg, Datum.d_self]; ring
  | invNe₁ i j ν _ =>
    exact ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy (by rw [gsum_append]; simp))
      (idg_mem_gdeg D sy _ _)⟩
  | invNe₂ i j ν _ =>
    exact ⟨0, Submodule.sub_mem _ (dg_mem_gdeg D sy (by rw [gsum_append]; simp))
      (idg_mem_gdeg D sy _ _)⟩
  | invP₁ i ν _ =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _
      (dg_mem_gdeg D sy (by rw [gsum_append]; simp)))
      (Submodule.sum_mem _ fun n _ => dg_mem_gdeg D sy ?_)) (idg_mem_gdeg D sy _ _)⟩
    rw [gsum_append, gsum_epsL, gsum_dcupL]; ring
  | invP₂ i ν _ =>
    exact ⟨0, Submodule.add_mem _ (dg_mem_gdeg D sy (by rw [gsum_append]; simp))
      (idg_mem_gdeg D sy _ _)⟩
  | invP₃ i ν m _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | invP₄ i ν n _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | invP₅ i ν m n _ _ =>
    refine ⟨2 * sy.d i * (m - n), Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) ?_⟩
    · rw [gsum_append, gsum_epsL, gsum_dcupL]; ring
    · split_ifs with hmn
      · subst hmn; rw [sub_self, mul_zero]; exact idg_mem_gdeg D sy _ _
      · exact Submodule.zero_mem _
  | invM₁ i ν _ =>
    refine ⟨0, Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.neg_mem _
      (dg_mem_gdeg D sy (by rw [gsum_append]; simp)))
      (Submodule.sum_mem _ fun n _ => dg_mem_gdeg D sy ?_)) (idg_mem_gdeg D sy _ _)⟩
    rw [gsum_append, gsum_etaL, gsum_dcapL]; ring
  | invM₂ i ν _ =>
    exact ⟨0, Submodule.add_mem _ (dg_mem_gdeg D sy (by rw [gsum_append]; simp))
      (idg_mem_gdeg D sy _ _)⟩
  | invM₃ i ν m _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | invM₄ i ν n _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | invM₅ i ν m n _ _ =>
    refine ⟨2 * sy.d i * (m - n), Submodule.sub_mem _ (dg_mem_gdeg D sy ?_) ?_⟩
    · rw [gsum_append, gsum_etaL, gsum_dcapL]; ring
    · split_ifs with hmn
      · subst hmn; rw [sub_self, mul_zero]; exact idg_mem_gdeg D sy _ _
      · exact Submodule.zero_mem _
  | dcupZero i ν n _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩
  | dcapZero i ν n _ => exact ⟨_, dg_mem_gdeg D sy rfl⟩

end OddMath.SKM

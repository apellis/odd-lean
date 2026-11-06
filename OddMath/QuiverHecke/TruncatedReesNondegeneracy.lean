/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.VacuumRouteSwappedRightNegative
import OddMath.QuiverHecke.SwappedAssembly.SupportedActionInputsOver
import OddMath.QuiverHecke.TruncatedReesGrading
import OddMath.SKM.BWWGradedParameters

/-! # The conjecture over graded bases and for truncated Rees parameters

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture, for the inhomogeneous parameters of (1.6) whose coefficient degrees
are nonnegative (`Scalars.LowerDegree`); J. Brundan, W. Wang, B. Webster, arXiv:2505.22929v2,
§2.2. Route of `docs/Nondegeneracy/Phase2Plan.md`.

The swapped vacuum route uses the parameters only through the two inputs of the supported
action (`SectorActionInputs`). Over a commutative coefficient ring graded in degrees
`0, …, b` by `K`-submodules, with the `tᵢⱼ` in degree `0` and each nonzero `sᵢⱼ^{pq}` with
`p < dᵢⱼ`, `q < dⱼᵢ` in its coefficient degree, these inputs hold (`probeActionInputsOver`).
The condition covers the whole box below the corners, including the terms with `p = 0` or
`q = 0` of the Brundan–Wang–Webster parameters, whose coefficient degree is positive
(`SKM.coefficientDegree_pos_of_pure`); the truncated Rees parameters satisfy it
(`truncatedRees_s_mem_box`). The truncations
`K[h]/(h^N)` of the Rees ring are such bases (`truncGrading`), which gives the truncated case
`TruncatedRees.TruncatedReesNondegeneracy`.

## Main results

* `nondegeneracy_of_sectorActionInputs`: the conjecture from the supported-action inputs of
  every finite-colour sector, over any commutative ring.
* `nondegeneracy_of_graded_base`: the conjecture over a base graded in degrees `0, …, b` for
  graded parameters.
* `truncatedReesNondegeneracy`: the conjecture for the truncated Rees parameters of every
  lower-degree parameter system over a field of characteristic zero.
* `gradedCoefficientNondegeneracy`: with `gradedCoefficientNondegeneracy_of_truncated`, the
  graded-coefficient statement `SKM.GradedCoefficientNondegeneracy`.

The datum is taken with colours and weights in one universe, as for the swapped route.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

namespace OddMath.QuiverHecke

universe u w

variable {I X : Type u} [AddCommGroup X]

/-- **The conjecture from the sector inputs.** Over any commutative ring, if the two inputs of
the supported action hold for every finite-colour sector, the Nondegeneracy Conjecture holds. -/
theorem nondegeneracy_of_sectorActionInputs {D : SKM.Datum I X} {K : Type u} [CommRing K]
    {Sc : SKM.Scalars D K} (hI : ∀ J, SectorActionInputs D Sc J) (cs : SKM.CScalars Sc) :
    SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_vacuum_route_sectors D Sc cs fun J tJ t'J hw μ d =>
    let ι : VacuumRouteIndex D := ⟨K, Sc, cs, J, hI J, tJ, t'J, hw, μ, d⟩
    ⟨(swappedRouteBases D ι).toSector (positiveBubbleField_swappedRouteBases D ι)
      (nonpositiveBubbleField_of_entries (swappedRightEntriesField D) ι)
      (swappedCoordinateField D ι) (swappedChartField D ι)⟩

section Graded
variable {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) {k : Type u} [CommRing k]
  {Sc : SKM.Scalars D k} {K : Type u} [CommRing K] [Algebra K k]
  (𝒜 : ℤ → Submodule K k) [GradedAlgebra 𝒜]
  (ht : ∀ i j, ((Sc.t i j : kˣ) : k) ∈ 𝒜 0)
  (hs : ∀ i j (p q : ℕ), (p : ℤ) < D.d i j → (q : ℤ) < D.d j i →
    Sc.s i j p q ≠ 0 → Sc.s i j p q ∈ 𝒜 (SKM.coefficientDegree sy i j p q))
  (b : ℤ) (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥)

include sy 𝒜 ht hs b h𝒜 in
/-- The sector inputs over a base graded in degrees `0, …, b`. -/
theorem sectorActionInputs_of_graded (J : Finset I) : SectorActionInputs D Sc J :=
  fun m cutoff bound ΛP ΛR hP hR =>
    SwappedAssembly.SupportedSectors.probeActionInputsOver _ _ m cutoff bound ΛP ΛR hP hR
      (ReservoirWeights.pairingExtensionSymmetrizer (D.restrictColours J) (sy.restrictColours J))
      𝒜 (fun i j => ht i.val j.val)
      (fun i j p q _ hp' _ hq' h0 => hs i.val j.val p q hp' hq' h0) b h𝒜

include sy 𝒜 ht hs b h𝒜 in
/-- **The conjecture over a graded base** (Brundan–Ellis, arXiv:1701.04133v2, §8): for a
symmetrizable datum and a commutative coefficient ring graded in degrees `0, …, b` by
`K`-submodules, with the `tᵢⱼ` in degree `0` and each nonzero `sᵢⱼ^{pq}` with `p < dᵢⱼ`,
`q < dⱼᵢ` in its coefficient degree, the Nondegeneracy Conjecture holds for every
normalization. -/
theorem nondegeneracy_of_graded_base (cs : SKM.CScalars Sc) : SKM.NondegeneracyConjecture cs :=
  nondegeneracy_of_sectorActionInputs (sectorActionInputs_of_graded sy 𝒜 ht hs b h𝒜) cs

end Graded

/-- The truncated Rees parameters are homogeneous of their coefficient degree on the whole box
`p < dᵢⱼ`, `q < dⱼᵢ`: in the interior by the lower-degree condition, and for `p = 0` or `q = 0`
because the coefficient degree is positive there (`SKM.coefficientDegree_pos_of_pure`). -/
theorem truncatedRees_s_mem_box {D : SKM.Datum I X} (sy : SKM.Symmetrizer D) {K : Type*}
    [CommRing K] {Sc : SKM.Scalars D K} (hl : Sc.LowerDegree sy) (N : ℕ) (i j : I)
    (p q : ℕ) (hp' : (p : ℤ) < D.d i j) (hq' : (q : ℤ) < D.d j i)
    (hs : (truncatedReesScalars D sy Sc N).s i j p q ≠ 0) :
    (truncatedReesScalars D sy Sc N).s i j p q ∈
      truncGrading K N (SKM.coefficientDegree sy i j p q) := by
  by_cases hpq : p = 0 ∨ q = 0
  · have hpos := SKM.coefficientDegree_pos_of_pure sy hp' hq' hpq
    have hm : (SKM.ReesParameters.scalars sy Sc).s i j p q ∈
        reesGrading K (SKM.coefficientDegree sy i j p q) :=
      C_mul_X_pow_mem_reesGrading _ _ (Int.toNat_of_nonneg hpos.le)
    rw [truncatedReesScalars_s]
    exact SKM.GradedImage.map_mem_image (f := truncAlg K N) hm
  · push Not at hpq
    exact truncatedRees_s_mem D sy hl N i j p q (by omega) hp' (by omega) hq' hs

/-- **The truncated case** (Brundan–Ellis, arXiv:1701.04133v2, §8, for the lower-degree
parameters of (1.6)): over every field of characteristic zero, for every lower-degree
parameter system, every normalization and every `N`, the Nondegeneracy Conjecture holds for the
Rees parameters truncated to `K[h]/(h^N)`. -/
theorem truncatedReesNondegeneracy (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) :
    SKM.TruncatedRees.TruncatedReesNondegeneracy D sy := by
  intro K _ _ Sc hl cs N
  letI := truncGradedAlgebra K N
  refine nondegeneracy_of_graded_base sy (truncGrading K N) (truncatedRees_t_mem D sy Sc N)
    (truncatedRees_s_mem_box sy hl N) N (fun m hm => ?_) _
  by_cases h : m < 0
  · exact truncGrading_eq_bot_of_neg K N h
  · exact truncGrading_eq_bot_of_le K N (not_lt.mp fun h' => hm ⟨not_lt.mp h, h'.le⟩)

/-- **The graded-coefficient statement** (Brundan–Ellis, arXiv:1701.04133v2, §8, for
graded-homogeneous parameters over `ℕ`-graded rings with `2` invertible), from the truncated
case. -/
theorem gradedCoefficientNondegeneracy (D : SKM.Datum I X) (sy : SKM.Symmetrizer D) :
    SKM.GradedCoefficientNondegeneracy.{u, u, w} D sy :=
  SKM.gradedCoefficientNondegeneracy_of_truncated (truncatedReesNondegeneracy D sy)

end OddMath.QuiverHecke

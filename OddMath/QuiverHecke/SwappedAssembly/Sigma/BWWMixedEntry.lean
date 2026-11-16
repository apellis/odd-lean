/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntrySourceUnits
import OddMath.SKM.BWWPureCoefficients
import OddMath.Algebra.NilpotentPerturbation

/-! # Distinct-colour mixed mates for Brundan–Wang–Webster parameters

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (1.11), with the
parameters `Qᵢⱼ(u, v) = Σ cᵢⱼ(p, q) u^p v^q` of Brundan–Wang–Webster, arXiv:2505.22929v2, §2.2.

`ProbeReservoir.isIso_homDistinctMixedMateDot_param_sourceUnits` proves that the dotted mixed
mate of `Qᵢⱼ` is invertible when `Qᵢⱼ = tᵢⱼ u^{dᵢⱼ} + (terms divisible by v)`, which is the
shape of the Brundan–Ellis parameters. For Brundan–Wang–Webster parameters `Qᵢⱼ(u, 0)` has
the lower terms `cᵢⱼ(p, 0) u^p`, `p < dᵢⱼ`. When these coefficients lie in a nilpotent ideal
`J` of `k` (`BWWScalars.PureIn`), their mate lies in `J • ⊤` and is absorbed by
`OddMath.Algebra.isIso_add_of_mem_smul`.

* `ProbeReservoir.isIso_homDistinctMixedMateDot_bwwParam_sourceUnits`: the dotted mixed mate of
  `Qᵢⱼ` is invertible under the source polynomial unit criterion, for any parities.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory

universe u uB vB wB

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X}

namespace ProbeReservoir

/-- `dᵢⱼ pᵢ ≠ 1` in `ZMod 2`: `dᵢⱼ` is even when `i` is odd. -/
theorem natCast_dn_mul_parity_ne_one (i j : I) :
    ((D.dn i j : ℕ) : ZMod 2) * D.parity i ≠ 1 := by
  rcases (show D.parity i = 0 ∨ D.parity i = 1 by
    generalize D.parity i = z; fin_cases z <;> simp) with h | h
  · rw [h, mul_zero]
    decide
  · rw [ScalarData.natCast_dn_eq_zero_of_odd h j, zero_mul]
    decide

/-- **The dotted mixed mate of a Brundan–Wang–Webster parameter polynomial.** For `i ≠ j`,
dots `x`, `y` of parities `pᵢ`, `pⱼ` satisfying the source polynomial unit criterion, and
pure coefficients in a nilpotent ideal, the dotted mixed mate of `Qᵢⱼ(X, Y)` is invertible. -/
theorem isIso_homDistinctMixedMateDot_bwwParam_sourceUnits {a b c d : B} (E : a ⟶ b)
    {E' : c ⟶ d} {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    (Sc : BWWScalars D k) {J : Ideal k} {N : ℕ} (hJ : J ^ N = ⊥) (hpure : Sc.PureIn J)
    {i j : I} (hij : i ≠ j) {x : E ⟶ E} (hx : x ∈ parity (R := k) E E (D.parity i))
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' (D.parity j))
    (hu : MixedPostSourceUnits E A κ H
      (rouquierPower x (if D.parity i = 1 then 2 else 1))
      (rouquierPower y (if D.parity j = 1 then 2 else 1))) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      (∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i + 1),
        Sc.c i j p q • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
          mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q))) := by
  have hx' : rouquierPower x (if D.parity i = 1 then 2 else 1) ∈ parity (R := k) E E 0 := by
    have h := rouquierPower_mem (k := k) hx (if D.parity i = 1 then 2 else 1)
    rwa [mul_parity_pow_eq_zero] at h
  have hy' : rouquierPower y (if D.parity j = 1 then 2 else 1) ∈ parity (R := k) E' E' 0 := by
    have h := rouquierPower_mem (k := k) hy (if D.parity j = 1 then 2 else 1)
    rwa [mul_parity_pow_eq_zero] at h
  set X := mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x
  set Y := mixedPostTargetPostDot (k := k) E κ H (F' := F') y
  have hmono : ∀ p q : ℕ, (p : ZMod 2) * D.parity i ≠ 1 → (q : ZMod 2) * D.parity j ≠ 1 →
      1 ≤ q → X ^ p * Y ^ q ∈ admissibleMonomials (k := k)
        (X ^ (if D.parity i = 1 then 2 else 1)) (Y ^ (if D.parity j = 1 then 2 else 1))
        (fun _ => True) (fun _ => True) 1 := by
    intro p q hp hq hq1
    obtain ⟨p', rfl⟩ := dvd_of_mul_parity_ne_one hp
    obtain ⟨q', rfl⟩ := dvd_of_mul_parity_ne_one hq
    refine Submodule.subset_span ⟨p', q', trivial, trivial, ?_, by rw [pow_mul, pow_mul]⟩
    rcases Nat.eq_zero_or_pos q' with h | h
    · simp [h] at hq1
    · exact h
  have hsplit := OddMath.Algebra.sum_box_split (Sc.c i j) (D.dn i j) (D.dn j i)
    (fun p q => X ^ p * Y ^ q)
  simp only [pow_zero, mul_one] at hsplit
  rw [hsplit, Sc.c_corner i j hij, add_right_comm ((Sc.t i j : k) • X ^ D.dn i j)]
  have hlin : ∀ Φ, homDistinctMixedMateDot E A κ τ H Φ =
      homDistinctMixedMateDotLinear E A κ τ H Φ := fun _ => rfl
  rw [hlin, map_add, ← hlin, ← hlin]
  obtain ⟨n, hn⟩ := dvd_of_mul_parity_ne_one (natCast_dn_mul_parity_ne_one (D := D) i j)
  have hN : ∑ p ∈ Finset.range (D.dn i j + 1), ∑ q ∈ Finset.range (D.dn j i),
      Sc.c i j p (q + 1) • (X ^ p * Y ^ (q + 1)) ∈ admissibleMonomials (k := k)
        (X ^ (if D.parity i = 1 then 2 else 1)) (Y ^ (if D.parity j = 1 then 2 else 1))
        (fun _ => True) (fun _ => True) 1 := by
    refine Submodule.sum_mem _ fun p _ => Submodule.sum_mem _ fun q _ => ?_
    by_cases hs : Sc.c i j p (q + 1) = 0
    · rw [hs, zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem _ _ (hmono p (q + 1) (fun h => hs (Sc.c_parity i j p (q + 1) h))
        (fun h => hs ((Sc.c_symm i j p (q + 1)).trans (Sc.c_parity j i (q + 1) p h)))
        (Nat.le_add_left 1 q))
  have hlead := isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu
    (Sc.t i j) n hN
  rw [← hn] at hlead
  have hM : homDistinctMixedMateDot E A κ τ H
      (∑ p ∈ Finset.range (D.dn i j), Sc.c i j p 0 • X ^ p) ∈
        J • (⊤ : Submodule k _) := by
    rw [hlin, map_sum]
    refine Submodule.sum_mem _ fun p hp => ?_
    rw [map_smul]
    exact Submodule.smul_mem_smul (hpure i j p hij (Finset.mem_range.mp hp)) Submodule.mem_top
  exact OddMath.Algebra.isIso_add_of_mem_smul J hJ _ hM

end ProbeReservoir

end OddMath.QuiverHecke.SwappedAssembly

import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntry
import OddMath.SKM.RouquierHomDistinctSourceUnits

/-! # Distinct-colour entries from source polynomial units

BE2 (1.11), in the swapped construction: the mixed entry only needs the
source polynomial unit criterion. The ELV application must discharge this
criterion using contentwise transpose bounds, rather than a global
nilpotence hypothesis. This module is an intermediate reduction.
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
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir

theorem isIso_homDistinctMixedMateDot_of_pow_sourceUnits {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {x : E ⟶ E} {y : E' ⟶ E'} {ex ey : ℕ}
    (hx : rouquierPower x ex ∈ parity (R := k) E E 0)
    (hy : rouquierPower y ey ∈ parity (R := k) E' E' 0)
    (hu : MixedPostSourceUnits E A κ H (rouquierPower x ex) (rouquierPower y ey)) (c : kˣ) (n : ℕ) {N}
    (hN : N ∈ admissibleMonomials (k := k)
      (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex)
      (mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey)
      (fun _ => True) (fun _ => True) 1) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      ((c : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ (ex * n) +
        N)) := by
  have hX : mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ ex =
      mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') (rouquierPower x ex) :=
    whiskerRight_rouquierPower (k := k) x _ ex
  have hY : mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ ey =
      mixedPostTargetPostDot (k := k) E κ H (F' := F') (rouquierPower y ey) := by
    rw [whiskerLeft_rouquierPower (k := k), rouquierPower_eq_pow, ← map_rouquierPower,
      rouquierPower_eq_pow, whiskerLeft_rouquierPower (k := k)]
  rw [hX, hY] at hN
  rw [pow_mul, hX]
  exact homDistinctMixedMateDot_isIso_of_sourceUnits E A κ τ H hx hy hu c n hN

/-- Source-unit form of `isIso_homDistinctMixedMateDot_param`, for parameters without pure terms
(`ScalarData.NoPure`, a hypothesis of this route; see `BWWMixedEntry` for the general box). -/
theorem isIso_homDistinctMixedMateDot_param_sourceUnits (hn : Sc.NoPure) {a b c d : B}
    (E : a ⟶ b) {E' : c ⟶ d}
    {F' : d ⟶ c} (A : SuperAdjunction (k := k) E' F') (κ τ : ZMod 2) (H : b ⟶ d)
    {i j : I} (hij : i ≠ j) {x : E ⟶ E} (hx : x ∈ parity (R := k) E E (D.parity i))
    {y : E' ⟶ E'} (hy : y ∈ parity (R := k) E' E' (D.parity j))
    (hu : MixedPostSourceUnits E A κ H
      (rouquierPower x (if D.parity i = 1 then 2 else 1))
      (rouquierPower y (if D.parity j = 1 then 2 else 1))) :
    IsIso (homDistinctMixedMateDot E A κ τ H
      (if D.d i j = 0 then (Sc.t i j : k) • (1 : End (E ≫ (homParityShift (k := k) κ).obj
          (((homParityShift (k := k) κ).obj H ≫ F') ≫ E'))) else
        (Sc.t i j : k) • mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^
            D.dn i j +
          (Sc.t j i : k) • mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ D.dn j i +
          ∑ p ∈ Finset.range (D.dn i j), ∑ q ∈ Finset.range (D.dn j i),
            Sc.s i j p q • (mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x ^ p *
              mixedPostTargetPostDot (k := k) E κ H (F' := F') y ^ q))) := by
  set ex := if D.parity i = 1 then 2 else 1
  set ey := if D.parity j = 1 then 2 else 1
  have hx' : rouquierPower x ex ∈ parity (R := k) E E 0 := by
    have h := rouquierPower_mem (k := k) hx ex
    rwa [mul_parity_pow_eq_zero] at h
  have hy' : rouquierPower y ey ∈ parity (R := k) E' E' 0 := by
    have h := rouquierPower_mem (k := k) hy ey
    rwa [mul_parity_pow_eq_zero] at h
  set X := mixedPostTargetPreDot (k := k) E κ H (E' := E') (F' := F') x
  set Y := mixedPostTargetPostDot (k := k) E κ H (F' := F') y
  have hmono : ∀ p q : ℕ, (p : ZMod 2) * D.parity i ≠ 1 → (q : ZMod 2) * D.parity j ≠ 1 →
      1 ≤ q → X ^ p * Y ^ q ∈ admissibleMonomials (k := k) (X ^ ex) (Y ^ ey)
        (fun _ => True) (fun _ => True) 1 := by
    intro p q hp hq hq1
    obtain ⟨p', rfl⟩ := dvd_of_mul_parity_ne_one hp
    obtain ⟨q', rfl⟩ := dvd_of_mul_parity_ne_one hq
    refine Submodule.subset_span ⟨p', q', trivial, trivial, ?_, by rw [pow_mul, pow_mul]⟩
    rcases Nat.eq_zero_or_pos q' with h | h
    · simp [h] at hq1
    · exact h
  split_ifs with hd
  · have h := isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu (Sc.t i j) 0
      (N := 0) (Submodule.zero_mem _)
    rwa [mul_zero, pow_zero, add_zero] at h
  · have hdij : D.d i j ≠ 0 := hd
    have hdji : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).mpr h)
    have hpar : ∀ {i j : I}, i ≠ j → D.d i j ≠ 0 →
        (D.dn i j : ZMod 2) * D.parity i ≠ 1 ∧ 1 ≤ D.dn i j := by
      intro i j hij hd
      have h₁ := D.dn_cast hij
      have h₃ := D.d_nonneg hij
      refine ⟨fun h => ?_, by omega⟩
      have hi : D.parity i = 1 := by
        rcases (show D.parity i = 0 ∨ D.parity i = 1 by
          generalize D.parity i = z; fin_cases z <;> simp) with h' | h'
        · rw [h', mul_zero] at h; exact absurd h (by decide)
        · exact h'
      obtain ⟨r, hr⟩ := D.even_d_of_odd hi j
      rw [hi, mul_one, ZMod.natCast_eq_one_iff_odd] at h
      obtain ⟨r', hr'⟩ := h
      omega
    obtain ⟨hpi, -⟩ := hpar hij hdij
    obtain ⟨hpj, hpos⟩ := hpar hij.symm hdji
    obtain ⟨n, hnd⟩ := dvd_of_mul_parity_ne_one hpi
    rw [add_assoc, hnd]
    refine isIso_homDistinctMixedMateDot_of_pow_sourceUnits E A κ τ H hx' hy' hu (Sc.t i j) n
      (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun p hp => Submodule.sum_mem _ fun q hq => ?_))
    · simpa only [pow_zero, one_mul] using hmono 0 (D.dn j i) (by simp) hpj hpos
    · by_cases hs : Sc.s i j p q = 0
      · rw [hs, zero_smul]; exact Submodule.zero_mem _
      · have hq1 : 1 ≤ q := by
          by_contra h0
          exact hs (hn i j p q hij (hnd ▸ Finset.mem_range.mp hp) (Finset.mem_range.mp hq)
            (Or.inr (by omega)))
        exact Submodule.smul_mem _ _ (hmono p q (fun h => hs (Sc.s_eq_zero i j p q h))
          (fun h => hs ((Sc.s_symm i j p q).trans (Sc.s_eq_zero j i q p h))) hq1)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

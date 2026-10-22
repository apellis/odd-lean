/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.TensorCorner
import OddMath.QuiverHecke.UpDown
import OddMath.QuiverHecke.UTurnSpanning
import Mathlib.Algebra.Ring.GeomSum

/-!
# Local corners modulo an ideal

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. Let `T` be a two-sided ideal of a `k`-algebra `R` and `E` a local corner of `R` with
identity `ε`. Every element of `E 0 + T` is nilpotent modulo `T` or invertible in the corner
modulo `T` (`LocalCorner.nilpotent_or_inverse_mod`).

For `E_s F_t 1_λ` the ideal is that of the endomorphisms through shorter words (`ShortSpan`),
and the elements to test are the endomorphisms of degree zero and parity zero:

* `upE_mem_gdeg`, `dnE_mem_gdeg`: the upward and downward placements preserve degree.
* `shortSpan_mul_left`, `shortSpan_mul_right`: the maps through shorter words form a two-sided
  ideal of `End(E_s F_t 1_λ)`.
* `proj0`, `proj0_mem_shortSpan`: the projection onto degree zero and parity zero preserves
  the maps through shorter words.
-/

namespace OddMath.SKM.GradedWalk

open Finset

variable {k R : Type*} [Field k] [Ring R] [Algebra k R]
  {E : Deg → Submodule k R} {ε : R} {NE : Submodule k R} {a lo : ℕ}

/-- `(x + t) ^ m - x ^ m` lies in a two-sided ideal containing `t`. -/
theorem add_pow_sub_pow_mem {T : Submodule k R} (hTl : ∀ r t, t ∈ T → r * t ∈ T)
    (hTr : ∀ t r, t ∈ T → t * r ∈ T) (x : R) {t : R} (ht : t ∈ T) (m : ℕ) :
    (x + t) ^ m - x ^ m ∈ T := by
  induction m with
  | zero => simp
  | succ m ih =>
    have e : (x + t) ^ (m + 1) - x ^ (m + 1) =
        ((x + t) ^ m - x ^ m) * (x + t) + x ^ m * t := by
      rw [pow_succ, pow_succ, sub_mul, mul_add, mul_add]; abel
    rw [e]
    exact T.add_mem (hTr _ _ ih) (hTl _ _ ht)

/-- **A local corner is local modulo an ideal.** An element `x + t` with `x ∈ E 0` and `t` in a
two-sided ideal `T` is nilpotent modulo `T`, or has an inverse `w ∈ E 0` in the corner modulo
`T`. -/
theorem LocalCorner.nilpotent_or_inverse_mod (hE : LocalCorner E ε NE a lo) {T : Submodule k R}
    (hTl : ∀ r t, t ∈ T → r * t ∈ T) (hTr : ∀ t r, t ∈ T → t * r ∈ T) {x t : R}
    (hx : x ∈ E 0) (ht : t ∈ T) :
    (x + t) ^ a ∈ T ∨ ∃ w ∈ E 0, (x + t) * w - ε ∈ T ∧ w * (x + t) - ε ∈ T := by
  obtain ⟨c, hc⟩ := hE.residue x hx
  have hpow : ∀ {n : R}, n ∈ NE → n ^ a = 0 := fun {n} hn => by
    have h := Submodule.pow_mem_pow NE hn a
    rwa [hE.rad_pow, Submodule.mem_bot] at h
  by_cases hc0 : c = 0
  · left
    rw [hc0, zero_smul, sub_zero] at hc
    have h := add_pow_sub_pow_mem hTl hTr x ht a
    rwa [hpow hc, sub_zero] at h
  · right
    set m : R := c⁻¹ • (x - c • ε) with hm
    have hmN : m ∈ NE := NE.smul_mem _ hc
    have hm0 : m ∈ E 0 := hE.rad_le hmN
    have hεm : ε * m = m := hE.unit_mul 0 m hm0
    have hmε : m * ε = m := hE.mul_unit 0 m hm0
    have hxe : x = c • (ε + m) := by
      rw [hm, smul_add, smul_smul, mul_inv_cancel₀ hc0, one_smul]; abel
    set g : R := ∑ i ∈ range a, (-m) ^ i with hg
    have hma : (-m) ^ a = 0 := by rw [neg_pow, hpow hmN, mul_zero]
    have hug : (1 + m) * g = 1 := by
      have := mul_neg_geom_sum (-m) a
      rwa [sub_neg_eq_add, hma, sub_zero] at this
    have hgu : g * (1 + m) = 1 := by
      have := geom_sum_mul_neg (-m) a
      rwa [sub_neg_eq_add, hma, sub_zero] at this
    have hεu : ε * (1 + m) = ε + m := by rw [mul_add, mul_one, hεm]
    have huε : (1 + m) * ε = ε + m := by rw [add_mul, one_mul, hmε]
    set w : R := c⁻¹ • (g * ε) with hw
    have hgε : g * ε ∈ E 0 := by
      rw [hg, sum_mul]
      refine Submodule.sum_mem _ fun i _ => ?_
      exact hE.pow_mul_le i (Submodule.mul_mem_mul
        (Submodule.pow_mem_pow NE (NE.neg_mem hmN) i) hE.unit_mem)
    have hεε : ε * ε = ε := hE.unit_mul 0 ε hE.unit_mem
    have hxw : x * w = ε := by
      rw [hxe, hw, smul_mul_smul_comm, mul_inv_cancel₀ hc0, one_smul, ← hεu, mul_assoc,
        ← mul_assoc (1 + m), hug, one_mul, hεε]
    have hwx : w * x = ε := by
      have h1 : ε * (ε + m) = (1 + m) * ε := by rw [mul_add, hεε, hεm, huε]
      rw [hxe, hw, smul_mul_smul_comm, inv_mul_cancel₀ hc0, one_smul, mul_assoc, h1,
        ← mul_assoc, hgu, one_mul]
    refine ⟨w, E 0 |>.smul_mem _ hgε, ?_, ?_⟩
    · rw [add_mul, hxw, add_sub_cancel_left]; exact hTr _ _ ht
    · rw [mul_add, hwx, add_sub_cancel_left]; exact hTl _ _ ht

end OddMath.SKM.GradedWalk

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams Presentation GradedWalk
open QuiverHecke (upWord)

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (sy : Symmetrizer D)

/-! ## Degrees of the placements -/

theorem upE_mem_gdeg (μ : X) (s : List I) (V : List (Letter I)) {n : ℤ} {x : End (hO Sc s)}
    (hx : x ∈ (QuiverHecke.pres D Sc).homDeg (QuiverHecke.gdeg D sy) _ _ n) :
    upE Sc μ s V x ∈ (pres D Sc).homDeg (gdeg D sy) (ob D μ (upWord s ++ V))
      (ob D μ (upWord s ++ V)) n := by
  have h := plcL_mem_gdeg (μ := μ) (u := []) (v := V) sy
    (QuiverHecke.alpha_mem_degree D Sc sy _ hx)
  simp only [List.nil_append] at h
  exact h

theorem dnE₀_mem_gdeg (ν : X) (t : List I) {n : ℤ} {y : End (hO Sc t)}
    (hy : y ∈ (QuiverHecke.pres D Sc).homDeg (QuiverHecke.gdeg D sy) _ _ n) :
    dnE₀ Sc ν t y ∈ (pres D Sc).homDeg (gdeg D sy) (ob D (-ν) (dnWord t))
      (ob D (-ν) (dnWord t)) n := by
  have h := omega_mem_gdeg sy (QuiverHecke.alpha_mem_degree D Sc sy ν hy)
  have h2 := comp_mem_homDeg (eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy)
    (omega_alpha_obj Sc ν t).symm) (comp_mem_homDeg h
      (eqToHom_mem_homDeg (P := pres D Sc) (gdeg D sy) (omega_alpha_obj Sc ν t)))
  simp only [zero_add, add_zero] at h2
  exact h2

theorem dnE_mem_gdeg (ν : X) (U : List (Letter I)) (t : List I) {n : ℤ} {y : End (hO Sc t)}
    (hy : y ∈ (QuiverHecke.pres D Sc).homDeg (QuiverHecke.gdeg D sy) _ _ n) :
    dnE Sc ν U t y ∈ (pres D Sc).homDeg (gdeg D sy) (ob D (-ν) (U ++ dnWord t))
      (ob D (-ν) (U ++ dnWord t)) n :=
  wordCast_mem_gdeg sy _ _ (plcL_mem_gdeg sy (dnE₀_mem_gdeg sy ν t hy))

/-! ## Endomorphisms through shorter words -/

variable (Sc) in
theorem shortSpan_mul_left (μ : X) (a : List (Letter I))
    (r : End ((pres D Sc).obj (ob D μ a))) {x : End ((pres D Sc).obj (ob D μ a))}
    (hx : x ∈ ShortSpan Sc μ a a) : r * x ∈ ShortSpan Sc μ a a := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, hu, g, h, rfl⟩ := hf
    refine Submodule.subset_span ⟨u, hu, g, h ≫ r, ?_⟩
    change (g ≫ h) ≫ r = _
    rw [Category.assoc]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx

variable (Sc) in
theorem shortSpan_mul_right (μ : X) (a : List (Letter I))
    (r : End ((pres D Sc).obj (ob D μ a))) {x : End ((pres D Sc).obj (ob D μ a))}
    (hx : x ∈ ShortSpan Sc μ a a) : x * r ∈ ShortSpan Sc μ a a := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, hu, g, h, rfl⟩ := hf
    refine Submodule.subset_span ⟨u, hu, r ≫ g, h, ?_⟩
    change r ≫ g ≫ h = _
    rw [Category.assoc]
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/-! ## The projection onto degree zero and parity zero -/

variable (hc : Sc.Homogeneous)

/-- The projection of a Hom-space onto its part of degree `0` and parity `0`. -/
def proj0 (μ : X) (a b : List (Letter I)) :
    ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) →ₗ[k]
      ((pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)) :=
  (homogeneousComponent (a := ob D μ a) (b := ob D μ b) (isParityHomogeneous D Sc)
    (0 : ZMod 2)).comp
    (homogeneousComponent (a := ob D μ a) (b := ob D μ b) (isHomogeneous_gdeg D sy Sc hc) (0 : ℤ))

variable {sy hc}

theorem proj0_eq_or {μ : X} {a b : List (Letter I)} {n : ℤ} {p : ZMod 2}
    {x : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (h₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ n)
    (h₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ p) :
    proj0 sy hc μ a b x = x ∨ proj0 sy hc μ a b x = 0 := by
  simp only [proj0, LinearMap.comp_apply]
  by_cases hn : n = 0
  · subst hn
    rw [homogeneousComponent_of_mem _ h₁]
    by_cases hp : p = 0
    · subst hp; exact Or.inl (homogeneousComponent_of_mem _ h₂)
    · exact Or.inr (homogeneousComponent_of_mem_of_ne _ h₂ hp)
  · rw [homogeneousComponent_of_mem_of_ne _ h₁ hn, map_zero]
    exact Or.inr rfl

theorem proj0_of_mem {μ : X} {a b : List (Letter I)}
    {x : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (h₁ : x ∈ (pres D Sc).homDeg (gdeg D sy) _ _ 0)
    (h₂ : x ∈ (pres D Sc).homDeg (parityDeg (sig D)) _ _ 0) :
    proj0 sy hc μ a b x = x := by
  simp only [proj0, LinearMap.comp_apply]
  rw [homogeneousComponent_of_mem _ h₁, homogeneousComponent_of_mem _ h₂]

theorem proj0_comp_mem_shortSpan {μ : X} {a b u : List (Letter I)}
    (hu : u.length + 2 ≤ a.length) (g : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ u))
    (h : (pres D Sc).obj (ob D μ u) ⟶ (pres D Sc).obj (ob D μ b)) :
    proj0 sy hc μ a b (g ≫ h) ∈ ShortSpan Sc μ a b := by
  refine (pres D Sc).hom_induction (p := fun g => proj0 sy hc μ a b (g ≫ h) ∈ _) ?_ ?_ ?_ ?_ g
  · intro d
    refine (pres D Sc).hom_induction
      (p := fun h => proj0 sy hc μ a b ((pres D Sc).diag d ≫ h) ∈ _) ?_ ?_ ?_ ?_ h
    · intro d'
      rcases proj0_eq_or (comp_mem_homDeg ((pres D Sc).diag_mem_homDeg (deg := gdeg D sy) d)
          ((pres D Sc).diag_mem_homDeg (deg := gdeg D sy) d'))
        (comp_mem_homDeg ((pres D Sc).diag_mem_homDeg (deg := parityDeg (sig D)) d)
          ((pres D Sc).diag_mem_homDeg (deg := parityDeg (sig D)) d')) with e | e <;> rw [e]
      · exact Submodule.subset_span ⟨u, hu, _, _, rfl⟩
      · exact Submodule.zero_mem _
    · rw [Limits.comp_zero, map_zero]; exact Submodule.zero_mem _
    · intro f₁ f₂ h₁ h₂
      rw [Preadditive.comp_add, map_add]; exact Submodule.add_mem _ h₁ h₂
    · intro r f hf
      rw [Linear.comp_smul, map_smul]; exact Submodule.smul_mem _ r hf
  · rw [Limits.zero_comp, map_zero]; exact Submodule.zero_mem _
  · intro f₁ f₂ h₁ h₂
    rw [Preadditive.add_comp, map_add]; exact Submodule.add_mem _ h₁ h₂
  · intro r f hf
    rw [Linear.smul_comp, map_smul]; exact Submodule.smul_mem _ r hf

/-- **The projection to degree zero preserves the maps through shorter words.** -/
theorem proj0_mem_shortSpan {μ : X} {a b : List (Letter I)}
    {x : (pres D Sc).obj (ob D μ a) ⟶ (pres D Sc).obj (ob D μ b)}
    (hx : x ∈ ShortSpan Sc μ a b) : proj0 sy hc μ a b x ∈ ShortSpan Sc μ a b := by
  induction hx using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨u, hu, g, h, rfl⟩ := hf
    exact proj0_comp_mem_shortSpan hu g h
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end OddMath.SKM

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.DividedPowerSpan
import OddMath.QuiverHecke.CornerImages
import Mathlib.RingTheory.Artinian.Ring

/-!
# The local corner of a primitive idempotent of a quiver Hecke superalgebra

Brundan–Ellis, arXiv:1701.04133v2, proof of Theorem 11.7, surjectivity, top step of the width
induction. Let `z` be an even degree-zero idempotent of `E_s` in `H` whose summand
`(E_s, z)` is indecomposable. The homogeneous pieces `γ ↦ z (End E_s)_γ z` form a local corner
(`LocalCorner`, from `TensorCorner`), with radical the image of the nilpotent endomorphisms of
the summand `(E_s, z)`, given two facts about the summand:

* the residue field is `k` (`hres`: every degree-zero even corner element is a scalar multiple of
  `z` plus a nilpotent);
* the summand is not isomorphic to its parity shift (`hodd`: there are no mutually inverse odd
  degree-zero corner elements).

Both are part of the analysis of the indecomposable summands of `E_s` in Theorem 11.3 and
Corollary 11.4, and are taken as hypotheses here. The other conditions are automatic: an
isomorphism of the summand with a nonzero degree shift of itself would make every power of a
degree-`n` corner element nonzero, against the lower bound on degrees in `H`.

* `heCorner z γ`: the corner `z (End E_s)_γ z`.
* `heRad`: the image of the nilpotent endomorphisms of `(E_s, z)`.
* `localCorner_heCorner`: the local corner.
-/

noncomputable section

open CategoryTheory StringDiagrams GradedSupercategory KrullSchmidt
open OddMath.SKM.Summands OddMath.SKM.GradedWalk

namespace OddMath.QuiverHecke

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : SKM.Datum I X}
  {k : Type w} [Field k] {Sc : SKM.Scalars D k} {sy : SKM.Symmetrizer D}
  {hc : Sc.Homogeneous} {s : List I}

/-! ## The corner families -/

variable (z : End (hObj D Sc sy hc s))

/-- The corner `z (End E_s) z`. -/
def cornerSub : Submodule k (End (hObj D Sc sy hc s)) where
  carrier := {x | z ≫ x ≫ z = x}
  add_mem' {a b} ha hb := by
    change z ≫ (a + b) ≫ z = a + b
    rw [Preadditive.add_comp, Preadditive.comp_add, ha, hb]
  zero_mem' := by
    change z ≫ (0 : End (hObj D Sc sy hc s)) ≫ z = 0
    simp
  smul_mem' c a ha := by
    change z ≫ (c • a) ≫ z = c • a
    rw [Linear.smul_comp, Linear.comp_smul, ha]

/-- The homogeneous corner `z (End E_s)_γ z`. -/
def heCorner (γ : Deg) : Submodule k (End (hObj D Sc sy hc s)) :=
  homPiece D Sc sy hc s s γ.1 γ.2 ⊓ cornerSub z

variable {z}

theorem mem_heCorner {γ : Deg} {x : End (hObj D Sc sy hc s)} :
    x ∈ heCorner z γ ↔ x ∈ homPiece D Sc sy hc s s γ.1 γ.2 ∧ z ≫ x ≫ z = x :=
  Iff.rfl

variable (hz : z ≫ z = z)
include hz

theorem corner_comp_left {x : End (hObj D Sc sy hc s)} (hx : z ≫ x ≫ z = x) : z ≫ x = x :=
  calc z ≫ x = z ≫ z ≫ x ≫ z := by rw [hx]
    _ = z ≫ x ≫ z := by rw [← Category.assoc, hz]
    _ = x := hx

theorem corner_comp_right {x : End (hObj D Sc sy hc s)} (hx : z ≫ x ≫ z = x) : x ≫ z = x :=
  calc x ≫ z = (z ≫ x ≫ z) ≫ z := by rw [hx]
    _ = z ≫ x ≫ z := by simp only [Category.assoc, hz]
    _ = x := hx

theorem heCorner_mul_mem {γ δ : Deg} {x y : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ)
    (hy : y ∈ heCorner z δ) : x * y ∈ heCorner z (γ + δ) := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have := comp_mem_degree hy.1.1 hx.1.1
    rwa [add_comm] at this
  · have := Supercategory.comp_mem hy.1.2 hx.1.2
    rwa [Prod.snd_add, add_comm]
  · change z ≫ (y ≫ x) ≫ z = y ≫ x
    rw [Category.assoc, corner_comp_right hz hx.2, ← Category.assoc,
      corner_comp_left hz hy.2]

theorem heCorner_pow_mem {γ : Deg} {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ)
    (n : ℕ) : x ^ (n + 1) ∈ heCorner z ((n + 1 : ℕ) • γ) := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact heCorner_mul_mem hz ih hx

theorem heCorner_one_mul {γ : Deg} {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ) :
    z * x = x :=
  corner_comp_right hz hx.2

theorem heCorner_mul_one {γ : Deg} {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ) :
    x * z = x :=
  corner_comp_left hz hx.2

theorem mem_heCorner_zero_self (hz0 : z ∈ homPiece D Sc sy hc s s 0 0) : z ∈ heCorner z 0 :=
  ⟨hz0, by change z ≫ z ≫ z = z; rw [hz, hz]⟩

/-! ## The summand `(E_s, z)` -/

section Summand

variable (hz0 : z ∈ homPiece D Sc sy hc s s 0 0)

/-- The summand `(E_s, z)`. -/
abbrev RZ := raw (k := k) hz hz0.1 hz0.2 0 0

/-- `evR` as a linear map on `End(E_s, z)`. -/
def evRL : End (RZ hz hz0) →ₗ[k] End (hObj D Sc sy hc s) where
  toFun := evR
  map_add' := evR_add
  map_smul' _ _ := rfl

theorem evRL_apply (φ : End (RZ hz hz0)) : evRL hz hz0 φ = evR φ := rfl

theorem evR_mul (φ ψ : End (RZ hz hz0)) : evR (φ * ψ) = evR ψ ≫ evR φ :=
  evR_comp ψ φ

theorem evR_one : evR (1 : End (RZ hz hz0)) = z := evR_id

theorem evR_mem_heCorner (φ : End (RZ hz hz0)) : evR φ ∈ heCorner z 0 :=
  ⟨⟨by simpa using evR_mem_degree φ, by simpa using evR_mem_parity φ⟩, evR_corner φ⟩

/-- A degree-zero even corner element, as an endomorphism of `(E_s, z)`. -/
def toR {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z 0) : End (RZ hz hz0) :=
  homR x (by simpa using hx.1.1) (by simpa using hx.1.2) hx.2

theorem evR_toR {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z 0) :
    evR (toR hz hz0 hx) = x := rfl

variable {hz hz0}

theorem z_ne_zero (hind : IsIndec (RZ hz hz0)) : z ≠ 0 := by
  intro h0
  apply hind.1
  rw [Limits.IsZero.iff_id_eq_zero]
  apply evR_injective
  exact h0

theorem heCorner_idem (hind : IsIndec (RZ hz hz0)) {e : End (hObj D Sc sy hc s)}
    (he : e ∈ heCorner z 0) (hee : e * e = e) : e = 0 ∨ e = z := by
  have hidem : toR hz hz0 he ≫ toR hz hz0 he = toR hz hz0 he :=
    evR_injective (by rw [evR_comp, evR_toR]; exact hee)
  rcases hind.2 _ hidem with h | h
  · left; rw [← evR_toR hz hz0 he, h]; rfl
  · right; rw [← evR_toR hz hz0 he, h]; rfl

/-- A one-sided inverse between opposite corner pieces is two-sided. -/
theorem heCorner_mul_eq_of_mul_eq (hind : IsIndec (RZ hz hz0)) {γ : Deg}
    {x v : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ) (hv : v ∈ heCorner z (-γ))
    (hxv : x * v = z) : v * x = z := by
  have he : v * x ∈ heCorner z 0 := by
    simpa using heCorner_mul_mem hz hv hx
  have hee : v * x * (v * x) = v * x := by
    rw [show v * x * (v * x) = v * (x * v) * x by simp only [mul_assoc], hxv,
      heCorner_mul_one hz hv]
  rcases heCorner_idem hind he hee with h | h
  · exfalso
    apply z_ne_zero hind
    calc z = z * z := hz.symm
      _ = x * v * (x * v) := by rw [hxv]
      _ = x * (v * x) * v := by simp only [mul_assoc]
      _ = 0 := by rw [h, mul_zero, zero_mul]
  · exact h

theorem heCorner_pow_mul_pow {γ : Deg} {x v : End (hObj D Sc sy hc s)}
    (hv : v ∈ heCorner z (-γ)) (hxv : x * v = z) (n : ℕ) :
    x ^ (n + 1) * v ^ (n + 1) = z := by
  induction n with
  | zero => simpa using hxv
  | succ n ih =>
    have hvn := heCorner_pow_mem hz hv n
    rw [pow_succ x (n + 1), pow_succ' v (n + 1),
      show x ^ (n + 1) * x * (v * v ^ (n + 1)) = x ^ (n + 1) * (x * v) * v ^ (n + 1) by
        simp only [mul_assoc], hxv, mul_assoc, heCorner_one_mul hz hvn, ih]

omit hz in
/-- The corner vanishes in sufficiently negative degrees. -/
theorem exists_heCorner_eq_bot :
    ∃ lo : ℕ, ∀ γ : Deg, γ.1 < -(lo : ℤ) → heCorner z γ = ⊥ := by
  obtain ⟨N, hN⟩ := homPiece_eq_bot_of_lt (D := D) (Sc := Sc) (sy := sy) (hc := hc) s s
  refine ⟨N.natAbs, fun γ hγ => ?_⟩
  rw [heCorner, hN γ.1 γ.2 (by omega), bot_inf_eq]

/-- **No summand is isomorphic to a nonzero shift of itself.** -/
theorem false_of_inverse (hind : IsIndec (RZ hz hz0))
    (hodd : ∀ x ∈ heCorner z ((0, 1) : Deg), ∀ u ∈ heCorner z ((0, 1) : Deg),
      x * u = z → u * x = z → False)
    {γ : Deg} (hγ : γ ≠ 0) {x v : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z γ)
    (hv : v ∈ heCorner z (-γ)) (hxv : x * v = z) (hvx : v * x = z) : False := by
  by_cases h1 : γ.1 = 0
  · have h2 : γ.2 = 1 := by
      have : γ.2 ≠ 0 := fun h => hγ (Prod.ext h1 h)
      rcases (show ∀ q : ZMod 2, q = 0 ∨ q = 1 by decide) γ.2 with h | h
      · exact absurd h this
      · exact h
    have hγ' : γ = ((0, 1) : Deg) := Prod.ext h1 h2
    have hnγ : -γ = ((0, 1) : Deg) := by rw [hγ']; rfl
    rw [hγ'] at hx
    rw [hnγ] at hv
    exact hodd x hx v hv hxv hvx
  · obtain ⟨lo, hlo⟩ := exists_heCorner_eq_bot (z := z)
    have key : ∀ {δ : Deg} {y w : End (hObj D Sc sy hc s)}, y ∈ heCorner z δ →
        w ∈ heCorner z (-δ) → y * w = z → δ.1 < 0 → False := by
      intro δ y w hy hw hyw hδ
      have hpow := heCorner_pow_mem hz hy lo
      have hbot : heCorner z ((lo + 1 : ℕ) • δ) = ⊥ := by
        apply hlo
        rw [Prod.smul_fst, nsmul_eq_mul]
        push_cast
        nlinarith
      rw [hbot, Submodule.mem_bot] at hpow
      apply z_ne_zero hind
      rw [← heCorner_pow_mul_pow (hz := hz) hw hyw lo, hpow, zero_mul]
    rcases lt_or_gt_of_ne h1 with h | h
    · exact key hx hv hxv h
    · exact key hv (by rwa [neg_neg]) hvx (by simpa using h)

theorem evR_toR_pow {b : End (hObj D Sc sy hc s)} (hb : b ∈ heCorner z 0) (n : ℕ) :
    evR (toR hz hz0 hb ^ (n + 1)) = b ^ (n + 1) := by
  induction n with
  | zero => rw [zero_add, pow_one, pow_one]; rfl
  | succ n ih => rw [pow_succ, evR_mul, ih, pow_succ b (n + 1)]; rfl

/-! ## The radical -/

section Radical

variable (hind : IsIndec (RZ hz hz0))
include hind

theorem false_of_nilpotent_of_isUnit_mul {φ y : End (RZ hz hz0)} (hφ : IsNilpotent φ)
    (hu : IsUnit (y * φ)) : False := by
  have := hind.nontrivial
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  have key : ∀ m : ℕ, (u * y) ^ m * φ ^ m = 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ', show (u * y) ^ m * (u * y) * (φ * φ ^ m) =
        (u * y) ^ m * (u * (y * φ)) * φ ^ m by simp only [mul_assoc], hu, mul_one, ih]
  have := key n
  rw [hn, mul_zero] at this
  exact zero_ne_one this

theorem false_of_nilpotent_of_isUnit_mul' {φ y : End (RZ hz hz0)} (hφ : IsNilpotent φ)
    (hu : IsUnit (φ * y)) : False := by
  have := hind.nontrivial
  obtain ⟨n, hn⟩ := hφ
  obtain ⟨u, hu⟩ := hu.exists_right_inv
  have key : ∀ m : ℕ, φ ^ m * (y * u) ^ m = 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, pow_succ', show φ ^ m * φ * (y * u * (y * u) ^ m) =
        φ ^ m * (φ * y * u) * (y * u) ^ m by simp only [mul_assoc], hu, mul_one, ih]
  have := key n
  rw [hn, zero_mul] at this
  exact zero_ne_one this

theorem isNilpotent_mul_left {φ : End (RZ hz hz0)} (hφ : IsNilpotent φ) (y : End (RZ hz hz0)) :
    IsNilpotent (y * φ) :=
  (hind.isNilpotent_or_isUnit k (y * φ)).resolve_right
    (false_of_nilpotent_of_isUnit_mul hind hφ)

theorem isNilpotent_mul_right {φ : End (RZ hz hz0)} (hφ : IsNilpotent φ) (y : End (RZ hz hz0)) :
    IsNilpotent (φ * y) :=
  (hind.isNilpotent_or_isUnit k (φ * y)).resolve_right
    (false_of_nilpotent_of_isUnit_mul' hind hφ)

theorem not_isUnit_of_isNilpotent {φ : End (RZ hz hz0)} (hφ : IsNilpotent φ) : ¬IsUnit φ :=
  fun hu => false_of_nilpotent_of_isUnit_mul hind hφ (y := 1) (by rwa [one_mul])

/-- The nilpotent endomorphisms of the indecomposable summand `(E_s, z)`. -/
def nilSub : Submodule k (End (RZ hz hz0)) where
  carrier := {φ | IsNilpotent φ}
  add_mem' {φ ψ} hφ hψ := by
    have := hind.isLocalRing k
    refine (hind.isNilpotent_or_isUnit k (φ + ψ)).resolve_right fun hu => ?_
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu with h | h
    · exact not_isUnit_of_isNilpotent hind hφ h
    · exact not_isUnit_of_isNilpotent hind hψ h
  zero_mem' := IsNilpotent.zero
  smul_mem' c φ hφ := by
    obtain ⟨n, hn⟩ := hφ
    exact ⟨n, by rw [smul_pow, hn, smul_zero]⟩

theorem nilSub_le_jacobson {φ : End (RZ hz hz0)} (hφ : φ ∈ nilSub hind) :
    φ ∈ (⊥ : Ideal (End (RZ hz hz0))).jacobson := by
  rw [Ideal.mem_jacobson_iff]
  intro y
  obtain ⟨u, hu⟩ := (isNilpotent_mul_left hind hφ y).isUnit_add_one
  refine ⟨↑u⁻¹, ?_⟩
  rw [Ideal.mem_bot, mul_assoc, ← mul_add_one, ← hu, Units.inv_mul, sub_self]

/-- **The radical**: the image of the nilpotent endomorphisms of `(E_s, z)`. -/
def heRad : Submodule k (End (hObj D Sc sy hc s)) :=
  (nilSub hind).map (evRL hz hz0)

theorem heRad_le : heRad hind ≤ heCorner z 0 := by
  rintro _ ⟨φ, -, rfl⟩
  exact evR_mem_heCorner hz hz0 φ

theorem heCorner_mul_heRad : heCorner z 0 * heRad hind ≤ heRad hind := by
  refine Submodule.mul_le.2 ?_
  rintro x hx _ ⟨φ, hφ, rfl⟩
  exact ⟨toR hz hz0 hx * φ, isNilpotent_mul_left hind hφ _, evR_mul hz hz0 _ _⟩

theorem heRad_mul_heCorner : heRad hind * heCorner z 0 ≤ heRad hind := by
  refine Submodule.mul_le.2 ?_
  rintro _ ⟨φ, hφ, rfl⟩ x hx
  exact ⟨φ * toR hz hz0 hx, isNilpotent_mul_right hind hφ _, evR_mul hz hz0 _ _⟩

theorem heRad_pow_le (i : ℕ) :
    heRad hind ^ (i + 1) ≤
      ((((⊥ : Ideal (End (RZ hz hz0))).jacobson) ^ (i + 1)).restrictScalars k).map
        (evRL hz hz0) := by
  have : IsScalarTower (End (RZ hz hz0)) (End (RZ hz hz0)) (End (RZ hz hz0)) :=
    IsScalarTower.left _
  induction i with
  | zero =>
    rw [zero_add, pow_one, Submodule.pow_one]
    rintro _ ⟨φ, hφ, rfl⟩
    exact ⟨φ, nilSub_le_jacobson hind hφ, rfl⟩
  | succ i ih =>
    rw [pow_succ (heRad hind)]
    refine (mul_le_mul' ih le_rfl).trans (Submodule.mul_le.2 ?_)
    rintro _ ⟨φ, hφ, rfl⟩ _ ⟨ψ, hψ, rfl⟩
    refine ⟨φ * ψ, ?_, evR_mul hz hz0 φ ψ⟩
    show φ * ψ ∈ (⊥ : Ideal (End (RZ hz hz0))).jacobson ^ (i + 1 + 1)
    rw [Submodule.pow_succ]
    exact Submodule.mul_mem_mul hφ (nilSub_le_jacobson hind hψ)

theorem exists_heRad_pow_eq_bot : ∃ a : ℕ, heRad hind ^ a = ⊥ := by
  have : FiniteDimensional k (End (RZ hz hz0)) := HomFinite.finiteDimensional _ _
  have : IsArtinianRing (End (RZ hz hz0)) := IsArtinianRing.of_finite k _
  obtain ⟨a, ha⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := End (RZ hz hz0))
  have : IsScalarTower (End (RZ hz hz0)) (End (RZ hz hz0)) (End (RZ hz hz0)) :=
    IsScalarTower.left _
  refine ⟨a + 1, eq_bot_iff.2 ((heRad_pow_le hind a).trans ?_)⟩
  rw [Submodule.pow_succ, ha, Submodule.zero_eq_bot, Submodule.bot_mul]
  rintro _ ⟨φ, hφ, rfl⟩
  have hφ' : φ ∈ (⊥ : Ideal (End (RZ hz hz0))) := hφ
  rw [Submodule.mem_bot] at hφ' ⊢
  rw [hφ']
  rfl

theorem residue_heRad (hres : ∀ a ∈ heCorner z 0, ∃ c : k, IsNilpotent (a - c • z))
    {x : End (hObj D Sc sy hc s)} (hx : x ∈ heCorner z 0) :
    ∃ c : k, x - c • z ∈ heRad hind := by
  obtain ⟨c, n, hn⟩ := hres x hx
  have hb : x - c • z ∈ heCorner z 0 :=
    Submodule.sub_mem _ hx (Submodule.smul_mem _ c (mem_heCorner_zero_self hz hz0))
  have hpow : toR hz hz0 hb ^ (n + 1) = 0 := by
    apply evR_injective
    rw [evR_toR_pow, pow_succ, hn, zero_mul]
    rfl
  exact ⟨c, toR hz hz0 hb, ⟨n + 1, hpow⟩, rfl⟩

theorem pair_le_heRad
    (hodd : ∀ x ∈ heCorner z ((0, 1) : Deg), ∀ u ∈ heCorner z ((0, 1) : Deg),
      x * u = z → u * x = z → False)
    {γ : Deg} (hγ : γ ≠ 0) : heCorner z γ * heCorner z (-γ) ≤ heRad hind := by
  refine Submodule.mul_le.2 fun x hx y hy => ?_
  have hw : x * y ∈ heCorner z 0 := by
    simpa using heCorner_mul_mem hz hx hy
  rcases hind.isNilpotent_or_isUnit k (toR hz hz0 hw) with hJ | hu
  · exact ⟨_, hJ, rfl⟩
  · exfalso
    obtain ⟨ψ, hψ⟩ := hu.exists_right_inv
    have h1 := congrArg evR hψ
    rw [evR_mul, evR_one] at h1
    have hv : y * evRL hz hz0 ψ ∈ heCorner z (-γ) := by
      have := heCorner_mul_mem hz hy (evR_mem_heCorner hz hz0 ψ)
      rwa [add_zero] at this
    have hxv : x * (y * evRL hz hz0 ψ) = z := by rw [← mul_assoc]; exact h1
    exact false_of_inverse hind hodd hγ hx hv hxv (heCorner_mul_eq_of_mul_eq hind hx hv hxv)

end Radical

/-- **The corner of a primitive idempotent of `H` is local**, given that its residue field is `k`
(`hres`) and that the summand is not isomorphic to its parity shift (`hodd`). -/
theorem localCorner_heCorner (hind : IsIndec (RZ hz hz0))
    (hres : ∀ a ∈ heCorner z 0, ∃ c : k, IsNilpotent (a - c • z))
    (hodd : ∀ x ∈ heCorner z ((0, 1) : Deg), ∀ u ∈ heCorner z ((0, 1) : Deg),
      x * u = z → u * x = z → False) :
    ∃ a lo : ℕ, LocalCorner (heCorner z) z (heRad hind) a lo := by
  obtain ⟨a, ha⟩ := exists_heRad_pow_eq_bot hind
  obtain ⟨lo, hlo⟩ := exists_heCorner_eq_bot (z := z)
  exact ⟨a, lo,
    { mul_le := fun γ δ => Submodule.mul_le.2 fun x hx y hy => heCorner_mul_mem hz hx hy
      unit_mem := mem_heCorner_zero_self hz hz0
      unit_mul := fun γ x hx => heCorner_one_mul hz hx
      mul_unit := fun γ x hx => heCorner_mul_one hz hx
      rad_le := heRad_le hind
      mul_rad := heCorner_mul_heRad hind
      rad_mul := heRad_mul_heCorner hind
      rad_pow := ha
      residue := fun x hx => residue_heRad hind hres hx
      pair_le := fun γ hγ => pair_le_heRad hind hodd hγ
      eq_bot := hlo }⟩

end Summand

end OddMath.QuiverHecke

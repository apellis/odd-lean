/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.ReservoirFusedVacuum
import OddMath.SKM.RouquierMateProjection

/-! # Normalized fused bubbles from the mate projection formula

Ports the vacuum bubble evaluation of
`Categorification/KLR/Unfurling/VacuumRouqBubbles.lean` and
`Categorification/KLR/Unfurling/GenericVacuumBubbles.lean` (images of the
bubbles of Rouquier data under evaluation at a vacuum object, read through an
algebra map), with the identification of the values of
`Categorification/KLR/Unfurling/GenericKLBubbles.lean`.

The even proof decomposes `F E` into scalar spectral labels. In the separated
super setting the two sectors are the nilpotent reservoir `A` and the
invertible probe `B`, and the only mixed term reaching the vacuum is the
`B → A` projection of the normalized mate `-q • rouquierMate`. This projection
is the first identity of `SKM.SuperRouquierLoc.MateProjectionFormula`, which
is used here as an explicit hypothesis and never proved or restated.

`mate_projection_sector_bubble` caps that identity by a probe cup and a
reservoir cap: the result is the ordered finite convolution of probe and
reservoir coefficients, with signs `q^r` and the probe on the source side.
`VacuumBubbleSector` evaluates it on the fused word modules. Its fields are of
two kinds: the identification of the capped mate composite with the fused
SKM bubble on the vacuum (the output of fusion inversion, A2), and the values
of the two factor coefficients on the identified regular modules (A0/A1).
`fused_bubbles_eq_reservoir` then derives `bubbles = reservoir` for every
generator, hence `NormalizedBubbleFormula`; for an odd colour the odd bubble
is the reservoir's own exterior coefficient (`fused_odd_bubble`).
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r

section Sector
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]

/-- The `B → A` mate projection, capped by a probe cup `κ` and a reservoir
cap `ℓ`, is the ordered convolution of probe and reservoir coefficients in
`End (𝟙 b)`. Composition is bottom to top, so the probe coefficient
`κ ≫ v_{B,-r-1}` is applied first. No inverse is used. -/
theorem mate_projection_sector_bubble
    {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    {A₁ : SKM.SuperAdjunction (k := k) E₁ F₁} {A₂ : SKM.SuperAdjunction (k := k) E₂ F₂}
    {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {XA XB YA YB : b ⟶ b}
    {inA : XA ⟶ F₁ ≫ E₁} {inB : XB ⟶ F₁ ≫ E₁}
    {outA : E₂ ≫ F₂ ⟶ YA} {outB : E₂ ≫ F₂ ⟶ YB}
    {uA : ℕ → (𝟙 b ⟶ YA)} {vA : ℕ → (XA ⟶ 𝟙 b)}
    {uB : ℤ → (𝟙 b ⟶ YB)} {vB : ℤ → (XB ⟶ 𝟙 b)} {nC nD : ℕ}
    (hM : SKM.SuperRouquierLoc.MateProjectionFormula A₁ A₂ t p
      inA inB outA outB uA vA uB vB nC nD)
    (κ : 𝟙 b ⟶ XB) (ℓ : YA ⟶ 𝟙 b) :
    κ ≫ inB ≫ (-(koszulSign p p) • SKM.rouquierMate A₁ A₂ t) ≫ outA ≫ ℓ =
      ∑ r ∈ Finset.range nC,
        (koszulSign p p) ^ r • ((κ ≫ vB (-(r : ℤ) - 1)) ≫ (uA r ≫ ℓ)) := by
  have h := congrArg (fun g => κ ≫ g ≫ ℓ) hM.1
  simp only [Category.assoc, Preadditive.comp_sum, Preadditive.sum_comp,
    Preadditive.comp_zsmul, Preadditive.zsmul_comp] at h ⊢
  exact h

end Sector

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} {cs : SKM.CScalars Sc}

/-- A probe series with scalar coefficients and constant term one is
normalized away by the triangular deconvolution: with probe values
`c_r = q^r P_r` the deconvolved reservoir coefficients satisfy the sector
normalization in degree `n`, for either parity. -/
theorem sector_normalize_deconvolution (p : ZMod 2) (P : ℕ → k) (hP : P 0 = 1)
    (C : ℕ → SKM.SYM D k) (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (koszulSign p p) ^ r •
      ((((koszulSign p p ^ r : ℤ) : k) * P r) •
        SKM.reservoirDeconvolution C (fun s => algebraMap k (SKM.SYM D k) (P s)) (n - r)) =
      C n := by
  have hq : ∀ r : ℕ, koszulSign p p ^ r * koszulSign p p ^ r = 1 := by
    intro r
    rw [← mul_pow]
    have : koszulSign p p * koszulSign p p = 1 := by
      unfold koszulSign; split_ifs <;> norm_num
    rw [this, one_pow]
  conv_rhs => rw [← SKM.reservoirConvolution_deconvolution C
    (fun s => algebraMap k (SKM.SYM D k) (P s)) (by simp [hP]) n]
  rw [SKM.reservoirConvolution]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Int.cast_smul_eq_zsmul k, smul_smul, ← mul_assoc, ← Int.cast_mul, hq,
    Int.cast_one, one_mul, Algebra.smul_def]
  exact Algebra.commutes _ _

/-- The separated-sector data for one coefficient generator `g` of `SYM`, at
the vacuum underlying the word modules `W`.

* The factor maps, sector inclusions/projections, dotted units/counits and
  truncation bounds are exactly the arguments of F's
  `SuperRouquierLoc.MateProjectionFormula` (`mateProjection`).
* `probeCup`/`reservoirCap` are the probe leftward cup and the reservoir
  leftward cap, and `eval t` is evaluation of vacuum 2-endomorphisms on the
  word module at `t`.
* `fused` (fusion inversion, A2): on every word module, the capped mate
  composite is the fused SKM bubble of the generator `g`.
* `probe` and `reservoirValue` (A0/A1): the probe coefficients act by
  scalars `c r`, and the reservoir coefficients by the identified reservoir
  coefficients `res r`.
* `normalize`: the scalar normalization `Σ_r q^r c_r res_r = g` in `SYM`;
  with a probe series having constant term one this is the triangular
  deconvolution of `ReservoirBubbleCoordinates.lean`. -/
structure VacuumBubbleSector {μ : X} (W : FusedVacuumWords D Sc cs μ)
    (reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)) (g : SKM.SYM D k)
    (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B] where
  a : B
  b : B
  c : B
  E₁ : a ⟶ b
  F₁ : b ⟶ a
  E₂ : b ⟶ c
  F₂ : c ⟶ b
  A₁ : SKM.SuperAdjunction (k := k) E₁ F₁
  A₂ : SKM.SuperAdjunction (k := k) E₂ F₂
  cross : E₁ ≫ E₂ ⟶ E₁ ≫ E₂
  p : ZMod 2
  XA : b ⟶ b
  XB : b ⟶ b
  YA : b ⟶ b
  YB : b ⟶ b
  inA : XA ⟶ F₁ ≫ E₁
  inB : XB ⟶ F₁ ≫ E₁
  outA : E₂ ≫ F₂ ⟶ YA
  outB : E₂ ≫ F₂ ⟶ YB
  uA : ℕ → (𝟙 b ⟶ YA)
  vA : ℕ → (XA ⟶ 𝟙 b)
  uB : ℤ → (𝟙 b ⟶ YB)
  vB : ℤ → (XB ⟶ 𝟙 b)
  nC : ℕ
  nD : ℕ
  probeCup : 𝟙 b ⟶ XB
  reservoirCap : YA ⟶ 𝟙 b
  eval : ∀ t, End (𝟙 b) →+* Module.End k (W.V t)
  fused : ∀ t, eval t (probeCup ≫ inB ≫
    (-(koszulSign p p) • SKM.rouquierMate A₁ A₂ cross) ≫ outA ≫ reservoirCap) = W.bubbles t g
  probeCoeff : ℕ → k
  res : ℕ → SKM.SYM D k
  probe : ∀ t (r : ℕ), eval t (probeCup ≫ vB (-(r : ℤ) - 1)) = algebraMap k _ (probeCoeff r)
  reservoirValue : ∀ t (r : ℕ), eval t (uA r ≫ reservoirCap) = reservoir t (res r)
  normalize : ∑ r ∈ Finset.range nC, (koszulSign p p) ^ r • (probeCoeff r • res r) = g

namespace VacuumBubbleSector
variable {μ : X} {W : FusedVacuumWords D Sc cs μ}
  {reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)} {g : SKM.SYM D k}
  {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  (S : VacuumBubbleSector W reservoir g B)

/-- F's projection obligation, applied verbatim to the sector data. -/
def mateProjection : Prop :=
  SKM.SuperRouquierLoc.MateProjectionFormula S.A₁ S.A₂ S.cross S.p
    S.inA S.inB S.outA S.outB S.uA S.vA S.uB S.vB S.nC S.nD

/-- C1 for one generator: the fused bubble acts as the reservoir coefficient. -/
theorem bubbles_eq (hM : S.mateProjection) (t : List I) :
    W.bubbles t g = reservoir t g := by
  refine (S.fused t).symm.trans (Eq.trans ?_ (congrArg (reservoir t) S.normalize))
  rw [mate_projection_sector_bubble hM, map_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_zsmul, map_zsmul, map_smul]
  congr 1
  have hmul : S.eval t ((S.probeCup ≫ S.vB (-(r : ℤ) - 1)) ≫ (S.uA r ≫ S.reservoirCap)) =
      S.eval t (S.uA r ≫ S.reservoirCap) * S.eval t (S.probeCup ≫ S.vB (-(r : ℤ) - 1)) :=
    (S.eval t).map_mul (show End (𝟙 S.b) from S.uA r ≫ S.reservoirCap)
      (show End (𝟙 S.b) from S.probeCup ≫ S.vB (-(r : ℤ) - 1))
  rw [hmul, S.probe, S.reservoirValue, Algebra.smul_def]
  exact (Algebra.commutes _ _).symm

end VacuumBubbleSector

/-- Sector data for every generator of `SYM`, all in one ambient
2-supercategory. -/
structure VacuumBubbleSectors {μ : X} (W : FusedVacuumWords D Sc cs μ)
    (reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t))
    (B : Type v) [BicategoryStruct.{w,w} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B] where
  sector : ∀ g : SKM.SYMGen D, VacuumBubbleSector W reservoir (SKM.SYM.ι D k g) B

namespace VacuumBubbleSectors
variable {μ : X} {W : FusedVacuumWords D Sc cs μ}
  {reservoir : ∀ t, SKM.SYM D k →ₐ[k] Module.End k (W.V t)}
  {B : Type v} [BicategoryStruct.{w,w} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  (S : VacuumBubbleSectors W reservoir B)

/-- The mate projection obligation for every generator sector. -/
def MateProjections : Prop := ∀ g, (S.sector g).mateProjection

/-- **Normalized fused bubbles.** From the mate projection formula, the
fused SKM bubbles act on every vacuum word module as the reservoir
coefficient algebra, including ordered products of odd generators. -/
theorem fused_bubbles_eq_reservoir (hM : S.MateProjections) (t : List I) :
    W.bubbles t = reservoir t :=
  SKM.SYM.hom_ext D k fun g => (S.sector g).bubbles_eq (hM g) t

/-- The odd bubble of an odd colour acts as the reservoir's exterior
coefficient, not as a probe parameter. -/
theorem fused_odd_bubble (hM : S.MateProjections) (t : List I)
    (i : {i : I // D.parity i = 1}) :
    W.act t t (SKM.bubAt D Sc μ (upWord t) (SKM.oddBubble cs i.1 μ)) =
      reservoir t (SKM.SYM.delta D k i) := by
  rw [← SKM.betaSYM_delta cs μ i, ← W.bubbles_eq, S.fused_bubbles_eq_reservoir hM t]

end VacuumBubbleSectors
end OddMath.QuiverHecke

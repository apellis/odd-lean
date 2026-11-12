/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedClosedCoefficients
import OddMath.QuiverHecke.VacuumRightBubbles
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles
import OddMath.SKM.BubblesNegativeHeight

/-! # Right bubbles at nonpositive height as source coefficients

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 2.3, (2.14),
(2.16)–(2.18), in the matrix form of `docs/Nondegeneracy/SwappedActionAssembly.md`.

At a nonpositive height `h = hᵢ(μ) ≤ 0` the normalized right bubbles `c_{μ;i} bubRs(n)` and
the odd bubble are closed diagrams:

* for `h < 0`, the cup `η` with `n - h - 1` dots followed by the cap `♦ε'` with `-h - 1` dots
  (`SKM.smul_bubRs_eq_cl_of_neg`);
* for `h = 0`, `c_{μ;i} bubRs(0)` is the identity (`SKM.smul_bubRs_zero_of_eq_zero`), and
  `c_{μ;i} bubRs(n + 1)` is minus the cup with `n` dots followed by the leftward crossing and
  the undotted cap: there `ε'` is a crossing followed by a cap
  (`SKM.smul_bubRs_succ_of_eq_zero`);
* the odd bubble is `c_{μ;i} bubRs(1)` (`SKM.oddBubble_eq_cl_of_neg`,
  `SKM.oddBubble_eq_cl_of_eq_zero`).

In the supported action on the tensor families these closed diagrams act as source
coefficients once their entries at the vacuum sector are coefficient actions
(`SupportedSectors.pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient`).
`SupportedSectors.VacuumRightEntries` collects these vacuum entries, and
`VacuumRightBubblesNonpositiveHeight.of_closed` turns the values of the closed action on these
diagrams into the right-bubble hypothesis `VacuumRightBubblesNonpositiveHeight` of the route,
for any upward action and raw coefficient map.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X} {k : Type w} [CommRing k]
  {Sc : Scalars D k} (cs : CScalars Sc)

/-- At negative height the normalized right bubble is one closed diagram: the cup with
`n - h - 1` dots followed by the cap `♦ε'` with `-h - 1` dots. -/
theorem smul_bubRs_eq_cl_of_neg (i : I) (μ : X) (hμ : D.h i μ < 0) (s : ℕ) :
    (cs.c μ i : k) • bubRs cs i μ s =
      cl D Sc μ [] []
        (etaL i ((s : ℤ) - D.h i μ - 1).toNat ++ dcapL i (-D.h i μ - 1).toNat) := by
  rw [smul_bubRs_of_neg cs i μ hμ s, cl_comp (sChain_etaL i _) (sChain_dcapL i _)]

/-- At height zero the normalized right bubble with no extra dots is the identity, (2.16). -/
theorem smul_bubRs_zero_of_eq_zero (i : I) (μ : X) (hμ : D.h i μ = 0) :
    (cs.c μ i : k) • bubRs cs i μ ((0 : ℕ) : ℤ) = 𝟙 _ := by
  have h₁ : ¬ (0 : ℤ) ≤ ((0 : ℕ) : ℤ) - D.h i μ - 1 := by omega
  have h₂ : ¬ -D.h i μ - 1 < ((0 : ℕ) : ℤ) - D.h i μ - 1 := by omega
  have h₃ : ((0 : ℕ) : ℤ) - D.h i μ - 1 = -D.h i μ - 1 := by omega
  rw [bubRs, bubR, ite_eq_right h₁, ite_eq_right h₂, ite_eq_left h₃, smul_smul,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]

/-- At height zero `ε'` is the leftward crossing followed by the undotted cap, so the
normalized right bubble with `n + 1` extra dots is minus the cup with `n` dots, the crossing
and the cap. -/
theorem smul_bubRs_succ_of_eq_zero (i : I) (μ : X) (hμ : D.h i μ = 0) (n : ℕ) :
    (cs.c μ i : k) • bubRs cs i μ ((n + 1 : ℕ) : ℤ) =
      -cl D Sc μ [] [] (etaL i n ++ (lcrossL i i ++ epsL i 0)) := by
  have h₁ : (0 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) - D.h i μ - 1 := by omega
  have h₂ : ¬ D.h i μ < 0 := by omega
  rw [bubRs, bubR, ite_eq_left h₁, epsP, ite_eq_right h₂, Linear.comp_smul,
    cl_comp (sChain_etaL i _) ((sChain_lcrossL i i).append (sChain_epsL i _))]
  have e₁ : (((n + 1 : ℕ) : ℤ) - D.h i μ - 1).toNat = n := by omega
  have e₂ : (D.h i μ).toNat = 0 := by omega
  rw [e₁, e₂, hμ, Int.cast_zero, mul_zero, zsign_zero, smul_smul, one_mul, mul_neg,
    ← Units.val_mul, mul_inv_cancel, Units.val_one, neg_smul, one_smul]

/-- At nonpositive height the odd bubble (2.18) is the normalized right bubble with one extra
dot. -/
theorem oddBubble_eq_smul_bubRs_of_nonpos (i : I) (μ : X) (hi : D.parity i = 1)
    (hμ : D.h i μ ≤ 0) :
    oddBubble cs i μ = (cs.c μ i : k) • bubRs cs i μ ((1 : ℕ) : ℤ) := by
  rcases hμ.lt_or_eq with h | h
  · exact oddBubble_of_neg cs i μ h
  · rw [oddBubble, ite_eq_left h.ge, show bubL cs i μ (D.h i μ) = bubL cs i μ 0 by rw [h],
      oddBubble_consistent cs i μ hi h, bubRs, show ((1 : ℕ) : ℤ) - D.h i μ - 1 = 0 by omega]

/-- At negative height the odd bubble is the cup with `-h` dots followed by `♦ε'`. -/
theorem oddBubble_eq_cl_of_neg (i : I) (μ : X) (hi : D.parity i = 1) (hμ : D.h i μ < 0) :
    oddBubble cs i μ =
      cl D Sc μ [] [] (etaL i (((1 : ℕ) : ℤ) - D.h i μ - 1).toNat ++
        dcapL i (-D.h i μ - 1).toNat) := by
  rw [oddBubble_eq_smul_bubRs_of_nonpos cs i μ hi hμ.le, smul_bubRs_eq_cl_of_neg cs i μ hμ 1]

/-- At height zero the odd bubble is minus the undotted cup, the leftward crossing and the
undotted cap. -/
theorem oddBubble_eq_cl_of_eq_zero (i : I) (μ : X) (hi : D.parity i = 1) (hμ : D.h i μ = 0) :
    oddBubble cs i μ = -cl D Sc μ [] [] (etaL i 0 ++ (lcrossL i i ++ epsL i 0)) := by
  rw [oddBubble_eq_smul_bubRs_of_nonpos cs i μ hi hμ.le]
  exact smul_bubRs_succ_of_eq_zero cs i μ hμ 0

end OddMath.SKM

namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u w
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : SKM.Datum I X} {Sc : SKM.Scalars D k} (cs : SKM.CScalars Sc)

/-- **Right bubbles at nonpositive height from closed diagrams.** For any upward action `A`
and any `raw`, the right-bubble hypothesis `VacuumRightBubblesNonpositiveHeight` follows from
the values of `A.closedAct` on the closed diagrams of `SKM.smul_bubRs_eq_cl_of_neg` and
`SKM.smul_bubRs_succ_of_eq_zero`. -/
theorem VacuumRightBubblesNonpositiveHeight.of_closed {μ : X}
    (A : UpwardModuleAction.{u, w} D Sc μ) (t : List I)
    (raw : SKM.SYM D k →ₐ[k] Module.End k (A.V t)) (M N' : I → ℕ)
    (neg_even : ∀ i, D.parity i = 0 → D.h i μ < 0 → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.etaL i ((s : ℤ) - D.h i μ - 1).toNat ++ SKM.dcapL i (-D.h i μ - 1).toNat)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    (zero_even : ∀ i, D.parity i = 0 → D.h i μ = 0 → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] [] (SKM.etaL i s ++ (SKM.lcrossL i i ++ SKM.epsL i 0))) =
      raw (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    (neg_odd : ∀ i, D.parity i = 1 → D.h i μ < 0 → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.etaL i (((2 * s : ℕ) : ℤ) - D.h i μ - 1).toNat ++
          SKM.dcapL i (-D.h i μ - 1).toNat)) =
      raw (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    (zero_odd : ∀ i, D.parity i = 1 → D.h i μ = 0 → ∀ s : ℕ,
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.etaL i (2 * s + 1) ++ (SKM.lcrossL i i ++ SKM.epsL i 0))) =
      raw (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i))))
    (odd_neg : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ < 0 →
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.etaL i.1 (((1 : ℕ) : ℤ) - D.h i.1 μ - 1).toNat ++
          SKM.dcapL i.1 (-D.h i.1 μ - 1).toNat)) =
      raw (SKM.SYM.probeSign D k N' i • SKM.SYM.delta D k i))
    (odd_zero : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ = 0 →
      A.closedAct t (SKM.cl D Sc μ [] []
        (SKM.etaL i.1 0 ++ (SKM.lcrossL i.1 i.1 ++ SKM.epsL i.1 0))) =
      raw (-(SKM.SYM.probeSign D k N' i • SKM.SYM.delta D k i))) :
    VacuumRightBubblesNonpositiveHeight cs A t raw M N' where
  right_even i hi hμ s := by
    rcases hμ.lt_or_eq with h | h
    · rw [SKM.smul_bubRs_eq_cl_of_neg cs i μ h s]
      exact neg_even i hi h s
    · cases s with
      | zero =>
        rw [SKM.smul_bubRs_zero_of_eq_zero cs i μ h,
          AdjunctionBubbleSeries.coeff_zero_momentSeries, map_one, map_one]
        exact (A.closedAct t).map_one
      | succ s =>
        rw [SKM.smul_bubRs_succ_of_eq_zero cs i μ h s, map_neg, zero_even i hi h s, map_neg,
          neg_neg]
  right_odd i hi hμ s := by
    rcases hμ.lt_or_eq with h | h
    · rw [show (2 * (s : ℤ)) = ((2 * s : ℕ) : ℤ) by push_cast; ring,
        SKM.smul_bubRs_eq_cl_of_neg cs i μ h (2 * s)]
      exact neg_odd i hi h s
    · cases s with
      | zero =>
        rw [show (2 * ((0 : ℕ) : ℤ)) = ((0 : ℕ) : ℤ) by simp,
          SKM.smul_bubRs_zero_of_eq_zero cs i μ h,
          AdjunctionBubbleSeries.coeff_zero_momentSeries, map_one, map_one]
        exact (A.closedAct t).map_one
      | succ s =>
        rw [show (2 * ((s + 1 : ℕ) : ℤ)) = ((2 * s + 1 + 1 : ℕ) : ℤ) by push_cast; ring,
          SKM.smul_bubRs_succ_of_eq_zero cs i μ h (2 * s + 1), map_neg, zero_odd i hi h s,
          map_neg, neg_neg]
  oddBubble i hμ := by
    rcases hμ.lt_or_eq with h | h
    · rw [SKM.oddBubble_eq_cl_of_neg cs i.1 μ i.2 h]
      exact odd_neg i h
    · rw [SKM.oddBubble_eq_cl_of_eq_zero cs i.1 μ i.2 h, map_neg, odd_zero i h, map_neg,
        neg_neg]

end OddMath.QuiverHecke

open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedRightBubbleCoefficientsHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

section Tensor
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (hF : ProbeActionInputs D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR)
  (sw : List I)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "c" => elvProbeCrossCoeffOf D Sc m cutoff N ΛP ΛR hP hR hF.dot
local notation "leftward" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR hF.dot
local notation "gens" => ProbeReservoir.swappedGens (P) c leftward
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "action" => pointwiseUpwardModuleAction D Sc m cutoff N ΛP ΛR hP hR hF.dot hF.window
  hF.pure (tensorSourceFamily D Sc m cutoff ΛP ΛR L sw) Ys
attribute [local irreducible] elvProbeCrossCoeffOf

/-- The entry of the closed diagram `M` at the vacuum sector of the tensor target family is the
coefficient action of `a` there. -/
def VacuumEntry (μ : X) (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M []) (a : SYM D k) :
    Prop :=
  ProbeReservoir.compDiag gens (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0))
    (Ys (0,0)).obj = (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom

/-- A closed diagram whose vacuum entry is the coefficient action of `a` acts as `a`. -/
theorem closedAct_cl_eq_coefficient (μ : X) (t : List I) (M : List (SKM.LayerData I))
    (hM : SKM.SChain [] M []) (a : SYM D k)
    (h : VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ M hM a) :
    (action μ).closedAct t (SKM.cl D Sc μ [] [] M) =
      tensorMatrixCoefficientAction D Sc m cutoff ΛP ΛR L sw (SKM.ob D μ (upWord t)) a :=
  pointwiseUpwardModuleAction_act_bubAt_cl_eq_coefficient D Sc m cutoff ΛP ΛR L hP hR hF sw
    μ t M hM a h

/-- **Vacuum entries of the right bubbles at nonpositive height.** The entries at the vacuum
sector of the closed diagrams of `SKM.smul_bubRs_eq_cl_of_neg`, `SKM.smul_bubRs_succ_of_eq_zero`
and of the odd bubble, as coefficient actions of the moments of `probeSeriesInv M` and of
`(-1)^(N_i+1) δ_i`. -/
structure VacuumRightEntries (μ : X) (M N' : I → ℕ) : Prop where
  neg_even : ∀ i, D.parity i = 0 → D.h i μ < 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i ((s : ℤ) - D.h i μ - 1).toNat ++ SKM.dcapL i (-D.h i μ - 1).toNat)
      ((SKM.sChain_etaL i _).append (SKM.sChain_dcapL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  zero_even : ∀ i, D.parity i = 0 → D.h i μ = 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i s ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
      ((SKM.sChain_etaL i _).append ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _)))
      (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  neg_odd : ∀ i, D.parity i = 1 → D.h i μ < 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i (((2 * s : ℕ) : ℤ) - D.h i μ - 1).toNat ++ SKM.dcapL i (-D.h i μ - 1).toNat)
      ((SKM.sChain_etaL i _).append (SKM.sChain_dcapL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  zero_odd : ∀ i, D.parity i = 1 → D.h i μ = 0 → ∀ s : ℕ,
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i (2 * s + 1) ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
      ((SKM.sChain_etaL i _).append ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _)))
      (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k M) i)))
  odd_neg : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ < 0 →
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i.1 (((1 : ℕ) : ℤ) - D.h i.1 μ - 1).toNat ++
        SKM.dcapL i.1 (-D.h i.1 μ - 1).toNat)
      ((SKM.sChain_etaL i.1 _).append (SKM.sChain_dcapL i.1 _))
      (SKM.SYM.probeSign D k N' i • SKM.SYM.delta D k i)
  odd_zero : ∀ i : {i : I // D.parity i = 1}, D.h i.1 μ = 0 →
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF μ
      (SKM.etaL i.1 0 ++ (SKM.lcrossL i.1 i.1 ++ SKM.epsL i.1 0))
      ((SKM.sChain_etaL i.1 _).append
        ((SKM.sChain_lcrossL i.1 i.1).append (SKM.sChain_epsL i.1 _)))
      (-(SKM.SYM.probeSign D k N' i • SKM.SYM.delta D k i))

end Tensor

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

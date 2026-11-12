/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumEntryLift
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumDecodeFaithful
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumCoefficientDecode
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumRightwardEvenMoments
import OddMath.QuiverHecke.SwappedVacuumAdjunctionBubbles

/-! # Vacuum entries of the even right bubbles at negative height

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

For an even colour `i` with `0 < M < N` (`M = m i`, `N = cutoff i`), so that the vacuum
height `h = M - N` is negative, the vacuum entry of the closed diagram
`η x^(s - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action of
the `s`-th coefficient of `(1 - w)^M / E(-w)` (`vacuumEntry_neg_even`). This is the field
`neg_even` of `VacuumRightNegativeEntries`.

The proof reads the entry on the tensor vacuum value through the cup inverse of
`tensorVacuum_rightward_even_bubbleEntries`, whose extreme column has the decoded moments of
`tensorVacuum_rightward_even_extreme_moments`, and lifts the decoded equality with
`vacuumEntry_of_decode`; faithfulness of the decoded reading is
`vacuumDecodeFaithful_tensorTarget`, and the decoded value of the coefficient action is
`vacuumDecode_tensorTargetCoefficient`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance supportedVacuumRightEvenHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (hF : ProbeActionInputs D Sc m cutoff (PowerWordContent.powerBound D cutoff L) ΛP ΛR hP hR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Ys" => tensorTargetFamily D Sc m cutoff ΛP ΛR L
local notation "cc" => elvProbeCrossCoeffOf D Sc m cutoff N ΛP ΛR hP hR hF.dot
local notation "lw" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR hF.dot

local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "Hv" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj Hv (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff N 0)
local notation "dec" => tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
local notation "Z" => (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj
local notation "Zt" => (tensorVacuum D Sc m cutoff L ΛP ΛR).obj
local notation "gens" => ProbeReservoir.swappedGens (P) cc lw

include hF in
/-- Conjugating the vacuum entry of a closed diagram along an equality of inputs. -/
private theorem conj_compDiag_even_of_eq {Z₁ Z₂ : (P).H ((0, 0) : Sector I)} (h : Z₁ = Z₂)
    (c : (E).obj Z₂ ≅ V) (μ : X) (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M []) :
    (eqToIso (congrArg (E).obj h) ≪≫ c).inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0)) Z₁) ≫
      (eqToIso (congrArg (E).obj h) ≪≫ c).hom =
    c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0)) Z₂) ≫ c.hom := by
  subst h
  simp

omit [Fintype I] in
private theorem even_probeCutoff_eq (i : I) (hi : D.parity i = 0) :
    probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

include hF in
/-- The negative inverse equations of the pointwise leftward data at the tensor vacuum
object. -/
private theorem vacuumNegEven_negInverseAt (i : I) (hh : D.h i ν₀ < 0) :
    (P).NegInverseAt cc i ν₀ ((0, 0) : Sector I) ((0, 0) : Sector I) Zt
      (fun q p => (lw).lcrossSame i ν₀ q p Zt)
      (fun n q r => (lw).dcap i n ν₀ q r Zt) :=
  have : Fact Sc.PureNilpotent := ⟨hF.pure⟩
  centralPointwiseLeftward_negInverseAt D Sc m cutoff N ΛP ΛR hP hR hF.dot hF.window i (0,0)
    (tensorVacuum D Sc m cutoff L ΛP ΛR) hh

local notation "Kc" => contentAppend D (parameterTwist D Sc) cutoff N (0 : Multiset I)

include hF in
/-- The decoded moments of the extreme column of an entrywise inverse of the native cup
window, in the coefficient action form. -/
private theorem vacuumNegEven_column (i : I) (hi : D.parity i = 0)
    (hP0 : 0 < probeCutoff D m i) (hPN : m i < cutoff i)
    (j : _ ⟶ ProbeVacuumCap.shiftedPreSourceObject D (parameterTwist D Sc) m
        (contentModuleTarget D (parameterTwist D Sc) cutoff N (0 : Multiset I)) i Hv)
    (B : Fin (cutoff i - m i) → (_ ⟶ V))
    (hB : ProbeWindow.IsCupInverse
      (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff N i hP0 Hv)
      (fun n => (BalancedInduction.adjunction (Kc [i])).unit.app V ≫
        (ProbeVacuumCap.evaluatedPostDot D (parameterTwist D Sc) m cutoff N i Hv ^ n.val)) j B)
    (s : ℕ) (z : (V).obj star) :
    dec (((BalancedInduction.adjunction (Kc [i])).unit.app V ≫
        (ProbeVacuumCap.evaluatedPostDot D (parameterTwist D Sc) m cutoff N i Hv ^
          (cutoff i - m i - 1 + s)) ≫ B ⟨cutoff i - m i - 1, by omega⟩).total star z) =
      coefficientPowerQuotientMap D cutoff L (SYM.polynomialInclude D k
        (PowerSeries.coeff s (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i))) *
        dec z := by
  have hm := tensorVacuum_rightward_even_extreme_moments D Sc m cutoff L i
      hF.dot hi hP0 hPN
    j B hB s z
  have e : ∀ p, polynomialToPower (k := k) D cutoff L p =
      coefficientPowerQuotientMap D cutoff L (SYM.polynomialInclude D k p) := fun _ => rfl
  rw [e] at hm
  exact hm

include hF in
/-- The even rightward bubble entries on the tensor vacuum object, for the pointwise
leftward data. -/
private theorem vacuumNegEven_bubble (i : I) (hi : D.parity i = 0)
    (hP0 : 0 < probeCutoff D m i) (hh : D.h i ν₀ < 0) :
    ∃ (c : _ ≅ V) (j : _ ⟶ ProbeVacuumCap.shiftedPreSourceObject D (parameterTwist D Sc) m
        (contentModuleTarget D (parameterTwist D Sc) cutoff N (0 : Multiset I)) i Hv)
      (B : Fin (cutoff i - m i) → (_ ⟶ V)),
      ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff N i hP0 Hv)
        (fun n => (BalancedInduction.adjunction (Kc [i])).unit.app V ≫
          (ProbeVacuumCap.evaluatedPostDot D (parameterTwist D Sc) m cutoff N i Hv ^ n.val))
        j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      (∀ (n : Fin (cutoff i - m i)) (e : ℕ),
        (BalancedInduction.adjunction (Kc [i])).unit.app V ≫
          (ProbeVacuumCap.evaluatedPostDot D (parameterTwist D Sc) m cutoff N i Hv ^ e) ≫
            B n =
        c.inv ≫ (E).map ((P).etaEntry cc i e ν₀ (.nil _)
            (SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I) ⟨false, trivial⟩)
            Zt ≫
          (lw).dcap i n ν₀ (SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I) ⟨false, trivial⟩)
            (.nil _) Zt) ≫ c.hom) :=
  have : Fact Sc.PureNilpotent := ⟨hF.pure⟩
  tensorVacuum_rightward_even_bubbleEntries D Sc m
    cutoff L ΛP ΛR hP hR i
      hF.dot hi hP0 Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm
    (fun q p => (lw).lcrossSame i ν₀ q p Zt)
    (fun n q r => (lw).dcap i n ν₀ q r Zt)
    (vacuumNegEven_negInverseAt D Sc m cutoff ΛP ΛR L hP hR hF i hh) cc

include hF in
/-- The decoded vacuum entry of `η x^e ≫ dcap n` at an even colour with negative vacuum
height, at the shifts `n = N - M - 1`, `e = n + s` read off the extreme moment column. -/
private theorem vacuumNegEven_decode (i : I) (hi : D.parity i = 0)
    (hP0 : 0 < probeCutoff D m i) (hh : D.h i ν₀ < 0) (s e n : ℕ)
    (hn : n = cutoff i - m i - 1) (he : e = cutoff i - m i - 1 + s) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (etaL i e ++ dcapL i n) ((sChain_etaL i e).append (sChain_dcapL i n)))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L (SYM.polynomialInclude D k
        (PowerSeries.coeff s (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i))) *
        dec z := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  rw [even_probeCutoff_eq D m i hi] at hhe
  have hh' := hh
  rw [hhe] at hh'
  have hPN : m i < cutoff i := by omega
  have hnZ : (n : ℤ) < -D.h i ν₀ := by rw [hhe, hn]; omega
  have hd : ¬StepValid (dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  have hZ : Z = Zt := by rw [tensorTargetFamily_zero]
  obtain ⟨c, j, B, hB, ⟨h0', hc0⟩, hcup⟩ :=
    vacuumNegEven_bubble D Sc m cutoff ΛP ΛR L hP hR hF i hi hP0 hh
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0', by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_even_of_eq D Sc m cutoff ΛP ΛR L hP hR hF hZ c,
    ProbeReservoir.compDiag_etaL_dcapL_swappedGens (P) _ _ i e n ν₀ hnZ (0,0) Zt hd]
  subst hn he
  have hcol := hcup ⟨cutoff i - m i - 1, by omega⟩ (cutoff i - m i - 1 + s)
  dsimp only [Fin.val_mk] at hcol
  have hm := vacuumNegEven_column D Sc m cutoff ΛP ΛR L hP hR hF i hi hP0 hPN j B hB s z
  rw [hcol] at hm
  exact hm

include hF in
/-- **Even right bubbles at negative height.** For an even colour `i` with
`0 < probeCutoff` and negative vacuum height `h`, the vacuum entry of
`η x^(s - h - 1) ≫ dcap (-h - 1)` of the tensor target family is the coefficient action of
the `s`-th coefficient of `(1 - w)^M / E(-w)`. -/
theorem vacuumEntry_neg_even (i : I) (hi : D.parity i = 0) (hP0 : 0 < probeCutoff D m i)
    (hh : D.h i ν₀ < 0) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR hF ν₀
      (etaL i ((s : ℤ) - D.h i ν₀ - 1).toNat ++ dcapL i (-D.h i ν₀ - 1).toNat)
      ((sChain_etaL i _).append (sChain_dcapL i _))
      (SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.momentSeries k (SYM.probeSeriesInv D k m) i))) := by
  have hhe := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  rw [even_probeCutoff_eq D m i hi] at hhe
  have hh' := hh
  rw [hhe] at hh'
  obtain ⟨c, hc', hf⟩ := vacuumNegEven_decode D Sc m cutoff ΛP ΛR L hP hR hF i hi hP0 hh s
    ((s : ℤ) - D.h i ν₀ - 1).toNat (-D.h i ν₀ - 1).toNat (by rw [hhe]; omega)
    (by rw [hhe]; omega)
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR hF _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

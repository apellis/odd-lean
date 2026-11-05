import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardEvenMoments
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumEntryLift
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumCoefficientDecode
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumDecodeFaithful
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumInverseWindow

/-!
# Left bubble entries of the vacuum sector

For an odd colour `i` with `0 < cutoff i` and positive height `h = ⟨hᵢ, ν₀⟩` at the vacuum
weight `ν₀` of the probe reservoir, the closed diagram `dcupL i (h-1) ++ epsL i (2s+h-1)`
(the left bubble of degree `2s`) acts on the vacuum sector of the tensor target family by
the `s`-th coefficient of the substituted probe series at `i`: the vacuum entry of the
odd left bubble used for the positive bubble field of the swapped route (Brundan–Ellis,
arXiv:1701.04133v2, bubble generating functions of the super Kac–Moody 2-category).

* `vacuumLeftOdd_decode`: the decoded vacuum entry, from the leftward odd moments
  `tensorVacuum_leftward_odd_moments` and the swapped generators' `dcupL`/`epsL` entry.
* `vacuumEntry_left_odd`: the `VacuumEntry` statement, by `vacuumEntry_of_decode`.
* `vacuumLeftEven_decode`, `vacuumEntry_left_even`: for an even colour, the closed diagram
  `dcupL i (h-1) ++ epsL i (s+h-1)` acts by the `s`-th substituted-series coefficient, from
  `tensorVacuum_leftward_even_moments`.
* `vacuumOddBubble_decode`, `vacuumEntry_oddBubble`: the odd bubble
  `dcupL i (h-1) ++ epsL i h` acts by `(-1)^(cutoff i + 1) δᵢ`, from the shift-`h` moment.
-/


noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance leftVacuumEntryHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Hv" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj Hv (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff N 0)
local notation "dec" => tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
local notation "Z" => (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj

variable (sy : Symmetrizer D) (hc : Sc.Homogeneous)
local notation "gens" => ProbeReservoir.swappedGens (P)
  (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc)
  (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc)

/-- Conjugating the vacuum entry of a closed diagram along an equality of inputs. -/
private theorem conj_compDiag_of_eq {Z₁ Z₂ : (P).H ((0, 0) : Sector I)} (h : Z₁ = Z₂)
    (c : (E).obj Z₂ ≅ V) (μ : X) (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M []) :
    (eqToIso (congrArg (E).obj h) ≪≫ c).inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0)) Z₁) ≫
      (eqToIso (congrArg (E).obj h) ≪≫ c).hom =
    c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0)) Z₂) ≫ c.hom := by
  subst h
  simp

include sy hc in
theorem vacuumLeftOdd_decode (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) (s : ℕ) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.dcupL i (D.h i ν₀ - 1).toNat ++
          SKM.epsL i (((2 * s : ℕ) : ℤ) + D.h i ν₀ - 1).toNat)
          ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _)))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.polynomialInclude D k
        (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i))) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hlt : cutoff i < probeCutoff D m i := by omega
  have hZ : Z = (tensorVacuum D Sc m cutoff L ΛP ΛR).obj := by rw [tensorTargetFamily_zero]
  obtain ⟨c, j, A, ⟨h0, hc0⟩, -, hcol, hmom⟩ :=
    tensorVacuum_leftward_odd_moments D Sc m cutoff L ΛP ΛR hP hR i
      (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
        (parameterTwist_homogeneous D Sc hc) _) hi hN hlt
      (fun q p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).lcrossSame i ν₀ q p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (fun n r p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).dcup i n ν₀ r p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (centralPointwiseLeftward_posInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
        (tensorVacuum D Sc m cutoff L ΛP ΛR) hpos.le)
      (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc)
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0, by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hn : (D.h i ν₀ - 1).toNat = probeCutoff D m i - cutoff i - 1 := by omega
  have hN' : (((2 * s : ℕ) : ℤ) + D.h i ν₀ - 1).toNat =
      probeCutoff D m i - cutoff i - 1 + 2 * s := by omega
  rw [hn, hN']
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  rw [ProbeReservoir.compDiag_dcupL_epsL_swappedGens (P) _ _ i _ _ _ (by omega) _ _ hu]
  have hcol' := hcol ⟨probeCutoff D m i - cutoff i - 1, by omega⟩
    (probeCutoff D m i - cutoff i - 1 + 2 * s)
  simp only [Fin.val_mk] at hcol'
  rw [← hcol']
  exact (hmom s z).1

include sy hc in
/-- **Odd left bubble entry of the vacuum sector.** -/
theorem vacuumEntry_left_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.dcupL i (D.h i ν₀ - 1).toNat ++
        SKM.epsL i (((2 * s : ℕ) : ℤ) + D.h i ν₀ - 1).toNat)
      ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i))) := by
  obtain ⟨c, hc', hf⟩ := vacuumLeftOdd_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN hpos s
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

include sy hc in
theorem vacuumOddBubble_decode (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.dcupL i (D.h i ν₀ - 1).toNat ++ SKM.epsL i (D.h i ν₀).toNat)
          ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _)))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L
        (SKM.SYM.probeSign D k cutoff ⟨i, hi⟩ • SKM.SYM.delta D k ⟨i, hi⟩) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hlt : cutoff i < probeCutoff D m i := by omega
  have hZ : Z = (tensorVacuum D Sc m cutoff L ΛP ΛR).obj := by rw [tensorTargetFamily_zero]
  obtain ⟨c, j, A, ⟨h0, hc0⟩, -, hcol, hmom⟩ :=
    tensorVacuum_leftward_odd_moments D Sc m cutoff L ΛP ΛR hP hR i
      (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
        (parameterTwist_homogeneous D Sc hc) _) hi hN hlt
      (fun q p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).lcrossSame i ν₀ q p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (fun n r p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).dcup i n ν₀ r p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (centralPointwiseLeftward_posInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
        (tensorVacuum D Sc m cutoff L ΛP ΛR) hpos.le)
      (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc)
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0, by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hn : (D.h i ν₀ - 1).toNat = probeCutoff D m i - cutoff i - 1 := by omega
  have hN' : (D.h i ν₀).toNat = probeCutoff D m i - cutoff i + 2 * 0 := by omega
  rw [hn, hN']
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  rw [ProbeReservoir.compDiag_dcupL_epsL_swappedGens (P) _ _ i _ _ _ (by omega) _ _ hu]
  have hcol' := hcol ⟨probeCutoff D m i - cutoff i - 1, by omega⟩
    (probeCutoff D m i - cutoff i + 2 * 0)
  simp only [Fin.val_mk] at hcol'
  rw [← hcol', (hmom 0 z).2,
    VacuumSeries.coeff_zero_substitutedSeries k (SKM.SYM.constantCoeff_probeSeries D k m),
    map_one, one_mul, map_smul, SKM.SYM.probeSign, smul_mul_assoc]

include sy hc in
/-- **Odd bubble entry of the vacuum sector at positive height.** -/
theorem vacuumEntry_oddBubble (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.dcupL i (D.h i ν₀ - 1).toNat ++ SKM.epsL i (D.h i ν₀).toNat)
      ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _))
      (SKM.SYM.probeSign D k cutoff ⟨i, hi⟩ • SKM.SYM.delta D k ⟨i, hi⟩) := by
  obtain ⟨c, hc', hf⟩ := vacuumOddBubble_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN hpos
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf


include sy hc in
/-- The decoded vacuum entry of the even left bubble of degree `s`. -/
theorem vacuumLeftEven_decode (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) (s : ℕ) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.dcupL i (D.h i ν₀ - 1).toNat ++
          SKM.epsL i ((s : ℤ) + D.h i ν₀ - 1).toNat)
          ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _)))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.polynomialInclude D k
        (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i))) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hlt : cutoff i < probeCutoff D m i := by omega
  have hZ : Z = (tensorVacuum D Sc m cutoff L ΛP ΛR).obj := by rw [tensorTargetFamily_zero]
  obtain ⟨c, j, A, ⟨h0, hc0⟩, -, hcol, hmom⟩ :=
    tensorVacuum_leftward_even_moments D Sc m cutoff L ΛP ΛR hP hR i
      (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
        (parameterTwist_homogeneous D Sc hc) _) hi hN hlt
      (fun q p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).lcrossSame i ν₀ q p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (fun n r p => (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc).dcup i n ν₀ r p
        (tensorVacuum D Sc m cutoff L ΛP ΛR).obj)
      (centralPointwiseLeftward_posInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
        (tensorVacuum D Sc m cutoff L ΛP ΛR) hpos.le)
      (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc)
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0, by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hn : (D.h i ν₀ - 1).toNat = probeCutoff D m i - cutoff i - 1 := by omega
  have hN' : ((s : ℤ) + D.h i ν₀ - 1).toNat =
      probeCutoff D m i - cutoff i - 1 + s := by omega
  rw [hn, hN']
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  rw [ProbeReservoir.compDiag_dcupL_epsL_swappedGens (P) _ _ i _ _ _ (by omega) _ _ hu]
  have hcol' := hcol ⟨probeCutoff D m i - cutoff i - 1, by omega⟩
    (probeCutoff D m i - cutoff i - 1 + s)
  simp only [Fin.val_mk] at hcol'
  rw [← hcol']
  exact hmom s z

include sy hc in
/-- **Even left bubble entry of the vacuum sector.** -/
theorem vacuumEntry_left_even (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (hpos : 0 < D.h i ν₀) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.dcupL i (D.h i ν₀ - 1).toNat ++ SKM.epsL i ((s : ℤ) + D.h i ν₀ - 1).toNat)
      ((SKM.sChain_dcupL i _).append (SKM.sChain_epsL i _))
      (SKM.SYM.polynomialInclude D k (PowerSeries.coeff s
        (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i))) := by
  obtain ⟨c, hc', hf⟩ := vacuumLeftEven_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN hpos s
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

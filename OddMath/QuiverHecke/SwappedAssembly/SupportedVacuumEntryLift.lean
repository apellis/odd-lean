/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.SupportedRightBubbleCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend

/-! # Vacuum entries from their decoded evaluation

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8
(the bubble relations of Definition 8.1 at the vacuum sector).

An endomorphism `f` of an object `Z` of the vacuum sector of the probe reservoir is
read on the tensor vacuum value `V` by evaluating with `vacuumSectorEvaluation`,
conjugating with an isomorphism `c : E Z ≅ V`, evaluating at the vacuum point and
reading in the decode chart (`vacuumDecode`). If this reading is injective
(`VacuumDecodeFaithful`), then two endomorphisms whose decoded values are both left
multiplication by the image of the same coefficient `a` are equal
(`eq_of_vacuumDecode`). In particular a compDiag entry at the vacuum sector of the
tensor target family is the coefficient action of `a` (`VacuumEntry`) as soon as its
decoded value and that of the coefficient action both are left multiplication by `a`
(`vacuumEntry_of_decode`). The statements do not depend on the height of the bubble
whose entry is considered. See `docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance supportedVacuumEntryLiftHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

section Lift
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (ΛP ΛR : X) (L : I × ℕ → ℕ)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff N ΛP ΛR hP hR
local notation "E" => vacuumSectorEvaluation D Sc m cutoff N ΛP ΛR hP hR
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff N
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff N (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff N 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L
local notation "dec" => tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L

/-- An endomorphism of an object of the vacuum sector, evaluated on the tensor vacuum
value through `c`, at the vacuum point, in the decode chart. -/
def vacuumDecode (Z : (P).H ((0, 0) : Sector I)) (c : (E).obj Z ≅ V) (f : Z ⟶ Z) :
    Module.End k AQ :=
  tensorVacuumEndDecode D (parameterTwist D Sc) m cutoff L (c.inv ≫ (E).map f ≫ c.hom)

/-- The decoded reading of endomorphisms of `Z` through `c` is injective. -/
def VacuumDecodeFaithful (Z : (P).H ((0, 0) : Sector I)) (c : (E).obj Z ≅ V) : Prop :=
  Function.Injective (vacuumDecode D Sc m cutoff ΛP ΛR L hP hR Z c)

/-- The decoded reading of `f` is left multiplication by `a` as soon as the decoded
values of `f` at the vacuum point are. -/
theorem vacuumDecode_eq_mulLeft (Z : (P).H ((0, 0) : Sector I)) (c : (E).obj Z ≅ V)
    (f : Z ⟶ Z) (a : SYM D k)
    (hf : ∀ z, dec ((c.inv ≫ (E).map f ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L a * dec z) :
    vacuumDecode D Sc m cutoff ΛP ΛR L hP hR Z c f =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a) :=
  tensorVacuumEndDecode_eq_of D (parameterTwist D Sc) m cutoff L _ _ hf

/-- Under faithfulness, endomorphisms with the same decoded values agree. -/
theorem eq_of_vacuumDecode (Z : (P).H ((0, 0) : Sector I)) (c : (E).obj Z ≅ V)
    (hfaith : VacuumDecodeFaithful D Sc m cutoff ΛP ΛR L hP hR Z c) {f g : Z ⟶ Z}
    (a : SYM D k)
    (hf : ∀ z, dec ((c.inv ≫ (E).map f ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L a * dec z)
    (hg : vacuumDecode D Sc m cutoff ΛP ΛR L hP hR Z c g =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a)) :
    f = g :=
  hfaith ((vacuumDecode_eq_mulLeft D Sc m cutoff ΛP ΛR L hP hR Z c f a hf).trans hg.symm)

variable (sy : Symmetrizer D) (hc : Sc.Homogeneous)

include sy hc in
/-- **Vacuum entries from decoded values.** If the decoded reading of the vacuum sector
of the tensor target family is faithful and the coefficient action of `a` decodes to
left multiplication by `a`, a closed diagram whose vacuum entry decodes to left
multiplication by `a` satisfies `VacuumEntry`. -/
theorem vacuumEntry_of_decode (μ : X) (M : List (SKM.LayerData I)) (hM : SKM.SChain [] M [])
    (a : SYM D k)
    (c : (E).obj (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj ≅ V)
    (hfaith : VacuumDecodeFaithful D Sc m cutoff ΛP ΛR L hP hR _ c)
    (hcoef : vacuumDecode D Sc m cutoff ΛP ΛR L hP hR _ c
      (tensorTargetFamilyCoefficientAction D Sc m cutoff L ΛP ΛR (0,0) a).hom =
      LinearMap.mulLeft k (coefficientPowerQuotientMap D cutoff L a))
    (hf : ∀ z, dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag
        (ProbeReservoir.swappedGens (P) (elvProbeCrossCoeffOf D Sc m cutoff N ΛP ΛR hP hR
    (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
      (parameterTwist_homogeneous D Sc hc) N))
          (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR
        (truncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff sy
          (parameterTwist_homogeneous D Sc hc) N)))
        (SKM.mkD D μ M hM) (SPath.nil (0,0)) (SPath.nil (0,0))
        (tensorTargetFamily D Sc m cutoff ΛP ΛR L (0,0)).obj) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L a * dec z) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc μ M hM a :=
  eq_of_vacuumDecode D Sc m cutoff ΛP ΛR L hP hR _ c hfaith a hf hcoef

end Lift

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

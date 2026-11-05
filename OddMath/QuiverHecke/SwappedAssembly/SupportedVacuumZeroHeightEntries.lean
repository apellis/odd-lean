/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCapMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCap
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitDotComponents
import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorFamilies
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumEntryLift
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumCoefficientDecode
import OddMath.QuiverHecke.SwappedAssembly.SupportedVacuumDecodeFaithful
import OddMath.QuiverHecke.SwappedAssembly.SupportedRightBubbleCoefficients
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCupInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseRightBubbleEntry
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumInverseWindow

/-!
# Right bubble entries of the vacuum sector at zero height

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, (2.16)–(2.18), toward the
nonpositive-height bubble identities of §8 (research issue #345).

At zero height `hᵢ(ν₀) = 0` the normalized right bubble `c bubRs(n + 1)` is minus the closed
diagram `etaL i n ++ (lcrossL i i ++ epsL i 0)`: the dotted unit, the leftward crossing and
the undotted cap. This file computes its entry at the vacuum sector of the tensor target
family.

* `ProbeReservoir.negInverseAt_of_posInverseAt_of_eq_zero`: at zero height the positive and
  negative augmented-inverse identities share their two nonempty equations, so the leftward
  data of `centralPointwiseLeftward_posInverseAt` also satisfies `NegInverseAt`.
* `ProbeReservoir.compDiag_etaL_lcrossL_epsL_swappedGens`: the entry of the closed diagram is
  the single product through the pure-reservoir paths.
* `ProbeReservoir.centralPadded_zeroHeight_bubbleEntry`: after an additive evaluation, the
  padded `σ` is invertible with inverse the padded `-lc` column, and the bubble entry is the
  unit row, the inverse and the cap row.
* `WeightTensorVacuum.vacuumZeroHeight_bubbleEntries`: the same in the native charts of the
  evaluated vacuum bend (`paddedVacuumDx_odd`/`_even`, `paddedVacuumUnit_native`,
  `paddedVacuumCap_native`).
* `SupportedSectors.vacuumEntry_zero_odd`, `vacuumEntry_zero_even`, `vacuumEntry_odd_zero`:
  the decoded entries are the moments of `tensorVacuumZeroHeightCap_*_moments`, the fields
  `zero_odd`, `zero_even` and `odd_zero` of `VacuumRightEntries`.

No inverse, moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false

namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM Classical

section Reservoir

universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}

namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
local instance zeroHeightPathFintype {w : List (Col I X)} {t s : Sector I} :
    Fintype (SPath w t s) :=
  Fintype.ofFinite _

/-- **Zero height: positive inverse identities give the negative ones.** When
`hᵢ(ν) = 0` both augmented windows are empty, and the two remaining identities of
`NegInverseAt` are those of `PosInverseAt` with sides exchanged. The column `dc'` of
the negative identities is arbitrary. -/
theorem negInverseAt_of_posInverseAt_of_eq_zero (c : P.CrossCoeff) (i : I) (ν : X)
    (t s : Sector I) (Z : P.H s)
    {lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z}
    {dc : ℕ → ∀ (_r : SPath (wd D ν []) t s) (p : SPath (wd D ν [up i, dn i]) t s),
      (P.pathFunctor _r).obj Z ⟶ (P.pathFunctor p).obj Z}
    (dc' : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t s) (r : SPath (wd D ν []) t s),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (h0 : D.h i ν = 0) (H : P.PosInverseAt c i ν t s Z lc dc) :
    P.NegInverseAt c i ν t s Z lc dc' := by
  unfold PosInverseAt at H
  unfold NegInverseAt
  obtain ⟨h1, h2, -, -, -⟩ := H
  have hp : (D.h i ν).toNat = 0 := by simp [h0]
  have hn : (-D.h i ν).toNat = 0 := by simp [h0]
  refine ⟨fun q q' => ?_, fun p p' => ?_, fun m hm => absurd hm (by omega),
    fun n hn' => absurd hn' (by omega), fun m n hm _ => absurd hm (by omega)⟩
  · rw [hn, Finset.range_zero, Finset.sum_empty, add_zero, h2 q q', neg_neg]
  · have h := h1 p p'
    rw [hp, Finset.range_zero, Finset.sum_empty, add_zero] at h
    rw [← h, neg_neg]

/-- **The zero-height right bubble entry at a probe-free sector.** Without a reservoir
summand of `Eᵢ` and a probe summand of `Fᵢ` at `t`, the entry of `η xᴺ`, the leftward
crossing and the undotted cap between empty paths is the single product through the
unique pure-reservoir paths of `FᵢEᵢ` and `EᵢFᵢ`. -/
theorem compDiag_etaL_lcrossL_epsL_swappedGens (c : P.CrossCoeff) (L : P.LeftwardData)
    (i : I) (N : ℕ) (ν : X) (t : Sector I) (Z : P.H t)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) :
    compDiag (P.swappedGens c L)
        (SKM.mkD D ν (SKM.etaL i N ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
          ((SKM.sChain_etaL i N).append
            ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i 0)))) (.nil t) (.nil t) Z =
      P.etaEntry c i N ν (.nil t) (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          Z ≫
        L.lcrossSame i ν (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) Z ≫
        P.epsEntry c i 0 ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
          (.nil t) Z := by
  have inner : ∀ q, compDiag (P.swappedGens c L)
      (SKM.mkD D ν (SKM.lcrossL i i ++ SKM.epsL i 0)
        ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i 0))) q (.nil t) Z =
      L.lcrossSame i ν q (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) Z ≫
        P.epsEntry c i 0 ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
          (.nil t) Z := by
    intro q
    rw [← SKM.mkD_comp D ν _ _ (SKM.sChain_lcrossL i i) (SKM.sChain_epsL i 0), compDiag_comp]
    refine Eq.trans (Fintype.sum_eq_single
      (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
      (fun b hb => absurd (SPath.eq_centralUpDn_true i ν t hu b) hb)) ?_
    rw [compDiag_lcrossL_swappedGens, compDiag_epsL_swappedGens]
  rw [← SKM.mkD_comp D ν _ _ (SKM.sChain_etaL i N)
    ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i 0)), compDiag_comp]
  refine Eq.trans (Fintype.sum_eq_single
    (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
    (fun b hb => absurd (SPath.eq_centralDnUp_false i ν t hd b) hb)) ?_
  rw [compDiag_etaL_swappedGens, inner]

variable {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]

/-- **Zero height in the padded chart.** If the negative inverse identities hold at
zero height, then after any additive evaluation the padded `σ` is invertible, with
inverse the padded column of `-lc`, and the evaluated zero-height bubble entry
`η xᴺ ≫ lc ≫ ε` is minus the padded unit row `N`, followed by that inverse and the
padded undotted cap row. -/
theorem centralPadded_zeroHeight_bubbleEntry (c : P.CrossCoeff) (i : I) (ν : X)
    (t : Sector I) (Z : P.H t) (E : P.H t ⥤ C) [E.Additive]
    (lc : ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (p : SPath (wd D ν [up i, dn i]) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (wd D ν [dn i, up i]) t t) (r : SPath (wd D ν []) t t),
      (P.pathFunctor _q).obj Z ⟶ (P.pathFunctor r).obj Z)
    (H : P.NegInverseAt c i ν t t Z lc dc)
    (hu : ¬StepValid (up i) false t) (hd : ¬StepValid (dn i) true t) (h0 : D.h i ν = 0) :
    ∃ J, P.centralPaddedSigma c i t Z E true false ≫ J = 𝟙 _ ∧
      J ≫ P.centralPaddedSigma c i t Z E true false = 𝟙 _ ∧
      ∀ N : ℕ, E.map (P.etaEntry c i N ν (.nil t)
          (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩) Z ≫
        lc (SPath.centralDnUp i (SKM.wt D ν [up i]) ν t ⟨false, trivial⟩)
          (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩) ≫
        P.epsEntry c i 0 ν (SPath.centralUpDn i (SKM.wt D ν [dn i]) ν t ⟨true, trivial⟩)
          (.nil t) Z) =
        -(P.centralPaddedUnit i t Z E false N ≫ J ≫ P.centralPaddedCap i t Z E true 0) := by
  obtain ⟨h1, -, -, -, h5⟩ :=
    P.isCupInverse_centralPadded_of_negInverseAt c i ν t Z E lc dc H hu hd
  have hn : (-D.h i ν).toNat = 0 := by simp [h0]
  have : IsEmpty (Fin (-D.h i ν).toNat) := by rw [hn]; infer_instance
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at h5
  refine ⟨_, h1, h5, fun N => ?_⟩
  rw [P.map_etaEntry_dcap_eq_padded c i ν t Z E _ N,
    P.epsEntry_centralFactor c i ν t Z ⟨true, trivial⟩ 0, centralPaddedCap,
    dite_eq_left (show StepValid (up i) true t from trivial)]
  simp only [Functor.map_comp, Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg,
    neg_neg, Category.assoc, Iso.inv_hom_id_assoc]

end ProbeReservoir

end Reservoir

end OddMath.QuiverHecke.SwappedAssembly

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance zeroHeightVacuumHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance zeroHeightContentZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Ev" => vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "cc" => elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩
local notation "Hb" => vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H
local notation "Kt" => contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)

/-- **Zero-height vacuum bubble entries in the native charts.** For leftward data
satisfying the negative inverse identities at zero height at an input equal to the
vacuum sector input, and an evaluated bend `b` presented by the padded `σ` in the native
charts (`paddedVacuumDx_odd` or `paddedVacuumDx_even`), `b` is invertible, and the
conjugated evaluated zero-height bubble entries `η xᴺ ≫ lc ≫ ε` are minus the native
unit-dot column `N`, followed by `b⁻¹` and the native cap. -/
theorem vacuumZeroHeight_bubbleEntries (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt cc i ν₀ ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (h0 : D.h i ν₀ = 0) (hP : 0 < probeCutoff D m i)
    (hDx : (P).centralPaddedSigma cc i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) Ev true false ≫
        (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP Hb) :
    ∃ (c : _ ≅ _) (j : _), (∃ h, c.hom = eqToHom h) ∧
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP Hb ≫ j =
        𝟙 _ ∧
      j ≫ ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP Hb =
        𝟙 _ ∧
      ∀ N : ℕ, c.inv ≫ (Ev).map ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ lc q₀ p₀ ≫
          (P).epsEntry cc i 0 ν₀ p₀ (.nil _) Z) ≫ c.hom =
        -(unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((Hb).obj (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫ j ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m Kt i hP Hb) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  obtain ⟨J, hJ1, hJ2, hent⟩ := (P).centralPadded_zeroHeight_bubbleEntry cc i ν₀
    ((0, 0) : Sector I) _ Ev lc dc HN hu hd h0
  have hb := (Iso.inv_comp_eq _).2 hDx
  have hC := paddedVacuumCap_native D Sc m cutoff bound ΛP ΛR hcP hcR H i hP 0
  rw [pow_zero, End.one_def, Category.id_comp] at hC
  refine ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H,
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫ J ≫
      (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H, ?_, ?_,
    fun N => ?_⟩
  · rw [← hb]
    simp [reassoc_of% hJ1]
  · rw [← hb]
    simp [reassoc_of% hJ2]
  · rw [hent N, (Iso.eq_comp_inv _).2 (paddedVacuumUnit_native D Sc m cutoff bound ΛP ΛR hcP hcR
      H i N)]
    simp only [Preadditive.neg_comp, Preadditive.comp_neg, Category.assoc,
      Iso.inv_hom_id_assoc, hC]

end Generic

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
open CyclotomicAction ELVOld ELVOld.PowerVacuumCoefficient ELVOld.WeightTensorVacuum
universe u
local instance zeroHeightEntryHomPi {k : Type u} [CommRing k]
    (A C : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C

private theorem zeroHeight_neg_total_apply {k : Type u} [CommRing k] {C : Type u}
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M N : Superfunctor k C (SVec k)} (f : M ⟶ N) (t : C) (b : M.obj t) :
    (-f).total t b = -(f.total t b) := by
  change -(f.app 0 t b) + -(f.app 1 t b) = -(f.app 0 t b + f.app 1 t b)
  exact (neg_add _ _).symm

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
local notation "Zt" => (tensorVacuum D Sc m cutoff L ΛP ΛR).obj

variable (sy : Symmetrizer D) (hc : Sc.Homogeneous)
local notation "gens" => ProbeReservoir.swappedGens (P)
  (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc)
  (pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc)
local notation "LD" => pointwiseLeftwardData D Sc m cutoff N ΛP ΛR hP hR sy hc

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
/-- The zero-height inverse data at the tensor vacuum: the leftward data satisfies
the negative inverse identities there. -/
private theorem zeroHeight_negInverseAt (i : I) (h0 : D.h i ν₀ = 0) :
    (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff N ΛP ΛR hP hR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Zt
      (fun q p => (LD).lcrossSame i ν₀ q p Zt) (fun _ _ _ => 0) :=
  ProbeReservoir.negInverseAt_of_posInverseAt_of_eq_zero (P) _ i ν₀ _ _ Zt _ h0
    (centralPointwiseLeftward_posInverseAt D Sc m cutoff N ΛP ΛR hP hR sy hc i (0,0)
      (tensorVacuum D Sc m cutoff L ΛP ΛR) h0.ge)

include sy hc in
/-- The decoded vacuum entry of the odd zero-height right bubble of degree `2s + 2`. -/
theorem vacuumZeroOdd_decode (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) (s : ℕ) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.etaL i (2 * s + 1) ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
          ((SKM.sChain_etaL i _).append
            ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _))))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L (-SKM.SYM.polynomialInclude D k
        (PowerSeries.coeff (s + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i))) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hpc : probeCutoff D m i = 2 * m i := by simp [probeCutoff, probeDotExponent, hi]
  have hcut : cutoff i = 2 * m i := by omega
  have hP' : 0 < probeCutoff D m i := by omega
  have hZ : Z = Zt := by rw [tensorTargetFamily_zero]
  have hex := vacuumZeroHeight_bubbleEntries D Sc m cutoff N ΛP ΛR hP hR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm
    (fun q p => (LD).lcrossSame i ν₀ q p Zt) (fun _ _ _ => 0)
    (zeroHeight_negInverseAt D Sc m cutoff ΛP ΛR L hP hR sy hc i h0) h0 hP'
    (paddedVacuumDx_odd D Sc m cutoff N ΛP ΛR hP hR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) i sy hc hP' hi)
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff N ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = Hv from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR] at hex
  obtain ⟨c, j, ⟨h0', hc0⟩, hj1, hj2, hcol⟩ := hex
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0', by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  rw [ProbeReservoir.compDiag_etaL_lcrossL_epsL_swappedGens (P) _ _ i _ _ _ _ hu hd,
    hcol, zeroHeight_neg_total_apply, map_neg, map_neg, neg_mul, neg_inj,
    BalancedInduction.unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  have e : ∀ p, polynomialToPower (k := k) D cutoff L p =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.polynomialInclude D k p) := fun _ => rfl
  have hm := tensorVacuumZeroHeightCap_odd_moments_odd D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP' hN hcut (Iso.mk _ j hj1 hj2) rfl s z
  rw [e] at hm
  convert hm using 6

include sy hc in
/-- **Odd zero-height right bubble entry of the vacuum sector.** -/
theorem vacuumEntry_zero_odd (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.etaL i (2 * s + 1) ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
      ((SKM.sChain_etaL i _).append ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _)))
      (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i))) := by
  obtain ⟨c, hc', hf⟩ := vacuumZeroOdd_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN h0 s
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

include sy hc in
/-- The decoded vacuum entry of the odd bubble at zero height. -/
theorem vacuumOddZero_decode (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.etaL i 0 ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
          ((SKM.sChain_etaL i _).append
            ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _))))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L
        (-(SKM.SYM.probeSign D k cutoff ⟨i, hi⟩ • SKM.SYM.delta D k ⟨i, hi⟩)) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hpc : probeCutoff D m i = 2 * m i := by simp [probeCutoff, probeDotExponent, hi]
  have hcut : cutoff i = 2 * m i := by omega
  have hP' : 0 < probeCutoff D m i := by omega
  have hZ : Z = Zt := by rw [tensorTargetFamily_zero]
  have hex := vacuumZeroHeight_bubbleEntries D Sc m cutoff N ΛP ΛR hP hR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm
    (fun q p => (LD).lcrossSame i ν₀ q p Zt) (fun _ _ _ => 0)
    (zeroHeight_negInverseAt D Sc m cutoff ΛP ΛR L hP hR sy hc i h0) h0 hP'
    (paddedVacuumDx_odd D Sc m cutoff N ΛP ΛR hP hR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) i sy hc hP' hi)
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff N ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = Hv from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR] at hex
  obtain ⟨c, j, ⟨h0', hc0⟩, hj1, hj2, hcol⟩ := hex
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0', by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  rw [ProbeReservoir.compDiag_etaL_lcrossL_epsL_swappedGens (P) _ _ i _ _ _ _ hu hd,
    hcol, zeroHeight_neg_total_apply, map_neg, map_neg, neg_mul, neg_inj,
    BalancedInduction.unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  have hm := tensorVacuumZeroHeightCap_odd_moments_even D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP' hN hcut (Iso.mk _ j hj1 hj2) rfl 0 z
  rw [Nat.mul_zero, AdjunctionBubbleSeries.coeff_zero_momentSeries,
    map_one, one_mul] at hm
  trace_state
  refine Eq.trans ?_ (hm.trans ?_)
  · rfl
  · rw [map_smul]
    rfl

include sy hc in
/-- **Odd bubble entry of the vacuum sector at zero height.** -/
theorem vacuumEntry_odd_zero (i : I) (hi : D.parity i = 1) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.etaL i 0 ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
      ((SKM.sChain_etaL i _).append ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _)))
      (-(SKM.SYM.probeSign D k cutoff ⟨i, hi⟩ • SKM.SYM.delta D k ⟨i, hi⟩)) := by
  obtain ⟨c, hc', hf⟩ := vacuumOddZero_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN h0
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

include sy hc in
/-- The decoded vacuum entry of the even zero-height right bubble of degree `s + 1`. -/
theorem vacuumZeroEven_decode (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) (s : ℕ) :
    ∃ c : (E).obj Z ≅ V, (∃ h, c.hom = eqToHom h) ∧ ∀ z,
      dec ((c.inv ≫ (E).map (ProbeReservoir.compDiag gens
        (SKM.mkD D ν₀ (SKM.etaL i s ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
          ((SKM.sChain_etaL i _).append
            ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _))))
        (SPath.nil (0,0)) (SPath.nil (0,0)) Z) ≫ c.hom).total star z) =
      coefficientPowerQuotientMap D cutoff L (-SKM.SYM.polynomialInclude D k
        (PowerSeries.coeff (s + 1)
          (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i))) * dec z := by
  have hh := vacuum_height_eq D Sc m cutoff N ΛP ΛR hP hR i
  have hpc : probeCutoff D m i = m i := by simp [probeCutoff, probeDotExponent, hi]
  have hcut : cutoff i = m i := by omega
  have hP' : 0 < probeCutoff D m i := by omega
  have hZ : Z = Zt := by rw [tensorTargetFamily_zero]
  have hex := vacuumZeroHeight_bubbleEntries D Sc m cutoff N ΛP ΛR hP hR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hP hR).symm
    (fun q p => (LD).lcrossSame i ν₀ q p Zt) (fun _ _ _ => 0)
    (zeroHeight_negInverseAt D Sc m cutoff ΛP ΛR L hP hR sy hc i h0) h0 hP'
    (paddedVacuumDx_even D Sc m cutoff N ΛP ΛR hP hR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) i sy hc hP' hi)
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff N ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = Hv from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR] at hex
  obtain ⟨c, j, ⟨h0', hc0⟩, hj1, hj2, hcol⟩ := hex
  refine ⟨eqToIso (congrArg (E).obj hZ) ≪≫ c, ⟨(congrArg (E).obj hZ).trans h0', by
    rw [Iso.trans_hom, eqToIso.hom, hc0, eqToHom_trans]⟩, fun z => ?_⟩
  rw [conj_compDiag_of_eq D Sc m cutoff ΛP ΛR L hP hR sy hc hZ c]
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by simp [StepValid]
  rw [ProbeReservoir.compDiag_etaL_lcrossL_epsL_swappedGens (P) _ _ i _ _ _ _ hu hd,
    hcol, zeroHeight_neg_total_apply, map_neg, map_neg, neg_mul, neg_inj,
    BalancedInduction.unitDotColumn_eq_restrictedDotEnd, Category.assoc]
  have e : ∀ p, polynomialToPower (k := k) D cutoff L p =
      coefficientPowerQuotientMap D cutoff L (SKM.SYM.polynomialInclude D k p) := fun _ => rfl
  have hm := tensorVacuumZeroHeightCap_even_moments D (parameterTwist D Sc) m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP' hN hcut (Iso.mk _ j hj1 hj2) rfl s z
  rw [e] at hm
  convert hm using 6

include sy hc in
/-- **Even zero-height right bubble entry of the vacuum sector.** -/
theorem vacuumEntry_zero_even (i : I) (hi : D.parity i = 0) (hN : 0 < cutoff i)
    (h0 : D.h i ν₀ = 0) (s : ℕ) :
    VacuumEntry D Sc m cutoff ΛP ΛR L hP hR sy hc ν₀
      (SKM.etaL i s ++ (SKM.lcrossL i i ++ SKM.epsL i 0))
      ((SKM.sChain_etaL i _).append ((SKM.sChain_lcrossL i i).append (SKM.sChain_epsL i _)))
      (-SKM.SYM.polynomialInclude D k (PowerSeries.coeff (s + 1)
        (VacuumSeries.momentSeries k (SKM.SYM.probeSeriesInv D k m) i))) := by
  obtain ⟨c, hc', hf⟩ := vacuumZeroEven_decode D Sc m cutoff ΛP ΛR L hP hR sy hc i hi hN h0 s
  exact vacuumEntry_of_decode D Sc m cutoff ΛP ΛR L hP hR sy hc _ _ _ _ c
    (vacuumDecodeFaithful_tensorTarget D Sc m cutoff ΛP ΛR L hP hR c)
    (vacuumDecode_tensorTargetCoefficient D Sc m cutoff ΛP ΛR L hP hR c hc' _) hf

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors

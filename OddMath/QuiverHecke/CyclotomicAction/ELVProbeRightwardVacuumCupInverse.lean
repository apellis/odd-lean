/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumUnit
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseCupInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseRightBubbleEntry
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # The rightward vacuum cup inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

At negative height `h_i(ν₀) < 0` of the vacuum sector, leftward data satisfying the
negative inverse equations (1.14) give an entrywise inverse of the padded cup window
`[σ, w₀, …]` (`isCupInverse_centralPadded_of_negInverseAt`). Evaluated by the vacuum
sector evaluation and read in the native charts of the regular vacuum probe, its
principal map is the evaluated A6 bend (odd colour, `paddedVacuumDx_odd`) and its
windows are the native dotted units `unitDotColumn` (`paddedVacuumUnit_eq`). The
columns of the inverse are explicit: the evaluated dotted rightward caps `dcap n`,
conjugated by the target and cap-target charts (`vacuumRightwardColumn`).
No inverse, moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

variable {C : Type*} [Category C] [Preadditive C]
  {X Y O O' : C} {n : ℕ} {s : X ⟶ Y} {u : Fin n → (O ⟶ Y)}
  {j : Y ⟶ X} {B : Fin n → (Y ⟶ O)}

/-- An isomorphism of the common window source transports a cup inverse. -/
theorem IsCupInverse.target (H : IsCupInverse s u j B) (c : O ≅ O') :
    IsCupInverse s (fun r => c.inv ≫ u r) j (fun r => B r ≫ c.hom) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨h1, fun r => ?_, fun r => ?_, fun r t => ?_, ?_⟩
  · rw [← Category.assoc, h2 r, Limits.zero_comp]
  · rw [Category.assoc, h3 r, Limits.comp_zero]
  · rw [Category.assoc, reassoc_of% (h4 r t)]
    split_ifs <;> simp
  · simpa only [Category.assoc, Iso.hom_inv_id_assoc] using h5

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance rightwardVacuumCupInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance rightwardVacuumCupInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "q₀" => SPath.centralDnUp i (SKM.wt D ν₀ [SKM.up i]) ν₀ ((0, 0) : Sector I)
  ⟨false, trivial⟩

/-- The explicit native column `n` of the rightward vacuum cup inverse: the dotted
rightward cap, evaluated by the vacuum sector evaluation and conjugated by the
padded target, corner and cap-target charts. -/
def vacuumRightwardColumn (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z) (n : ℕ) := by
  subst hZ
  exact ((paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
    ((P).centralTargetCornerIso i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, trivial⟩).hom ≫
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        (((P).centralTargetFactorIso i ν₀ ((0, 0) : Sector I)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨false, trivial⟩).hom ≫
          dc n q₀ (.nil _))) ≫
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom

include sy hc in
/-- **The rightward vacuum cup inverse in the native chart (odd colour).** Leftward
data satisfying the negative inverse equations at the vacuum sector give an
entrywise inverse of the native cup window `[bend, unit ≫ xⁿ]_(n < -h)` of the
evaluated A6 bend, `h = h_i(ν₀)`, whose columns are the explicit
`vacuumRightwardColumn`. -/
theorem vacuumRightwardCupInverse_odd (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ j, ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j
        (fun n => vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  haveI : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCupInverse_centralPadded_of_negInverseAt
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HN hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
      (P).centralPaddedUnit i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) false n ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) n := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumUnit_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i n)
  simp only [Iso.symm_hom, Iso.symm_inv] at h₃
  rw [hs] at h₃
  simp only [hw] at h₃
  exact ⟨_, h₃⟩

/-- The explicit native column, at the vacuum sector input itself. -/
theorem vacuumRightwardColumn_eq
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (n : ℕ) :
    vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n =
      ((paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
        ((P).centralTargetCornerIso i ((0, 0) : Sector I)
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
            (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨false, trivial⟩).hom ≫
          (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
            (((P).centralTargetFactorIso i ν₀ ((0, 0) : Sector I)
              (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨false, trivial⟩).hom ≫
              dc n q₀ (.nil _))) ≫
        (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom :=
  rfl

/-- **Native unit rows against the rightward columns.** The native dotted unit
`unit ≫ xᴺ` followed by the column `n` is the evaluated right bubble entry
`η xᴺ ≫ dcap n`, conjugated by the cap-target chart. -/
theorem vacuumRightwardColumn_unit (cc : (P).CrossCoeff)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (n N : ℕ) :
    unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
        (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
          (0 : Multiset I) i)
        ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
          (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫
      vacuumRightwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n =
    (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        ((P).etaEntry cc i N ν₀ (.nil _) q₀
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ≫
          dc n q₀ (.nil _)) ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom := by
  rw [vacuumRightwardColumn_eq, ← (Iso.inv_comp_eq _).2
    (paddedVacuumUnit_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i N),
    (P).map_etaEntry_dcap_eq_padded cc i ν₀ ((0, 0) : Sector I)
      (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (dc n q₀ (.nil _)) N]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

include sy hc in
/-- **Rightward vacuum cup inverse with bubble-entry columns.** For leftward data
satisfying the negative inverse equations at an input equal to the vacuum sector
input, the native cup window of the evaluated A6 bend has an entrywise inverse
whose products with the native unit rows `unit ≫ xᴺ` are the evaluated right bubble
entries `η xᴺ ≫ dcap n`, conjugated by one isomorphism `c`, which is an `eqToHom`. -/
theorem vacuumRightwardCupInverse_bubbleEntries (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor r).obj Z)
    (HN : (P).NegInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ (c : _ ≅ _) (j : _) (B : Fin (-D.h i ν₀).toNat → _),
      ProbeWindow.IsCupInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (-D.h i ν₀).toNat =>
          unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) n) j B ∧
      (∃ h, c.hom = eqToHom h) ∧
      ∀ (n : Fin (-D.h i ν₀).toNat) (N : ℕ),
        unitDotColumn (contentAppend D (parameterTwist D Sc) cutoff bound (0 : Multiset I) [i])
            (canonicalAppendDot_supernatural D (parameterTwist D Sc) cutoff bound
              (0 : Multiset I) i)
            ((vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H).obj
              (probeOldVacuumRegular D (parameterTwist D Sc) m)) N ≫ B n =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          ((P).etaEntry cc i N ν₀ (.nil _) q₀ Z ≫ dc n q₀ (.nil _)) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumRightwardCupInverse_odd D Sc m cutoff bound ΛP ΛR hcP hcR H
    sy hc i _ rfl lc dc HN hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _, hj,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H,
    fun n N => vacuumRightwardColumn_unit D Sc m cutoff bound ΛP ΛR hcP hcR H i cc dc n N⟩

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

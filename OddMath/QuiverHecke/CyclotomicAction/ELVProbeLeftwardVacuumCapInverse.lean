/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCapInverse
import OddMath.QuiverHecke.SwappedAssembly.Sigma.PointwiseBubbleEntry

/-! # The leftward vacuum cap inverse in the native chart

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

`vacuumCapInverse_odd` transports a cap inverse of the vacuum window to the
native chart, but only existentially. Here the inverse is the one given by any
leftward data satisfying the positive inverse equations at the vacuum sector
(`isCapInverse_centralPadded_of_posInverseAt`), evaluated directly by the vacuum
sector evaluation. Its columns are explicit: the dotted leftward cups, conjugated
by the source and cap-target charts (`vacuumLeftwardCapInverse_odd`).
Consequently every product of a column with a native cap row `x ^ N ≫ v` is the
conjugated evaluation of the left bubble entry `dcup n ≫ ε xᴺ`
(`vacuumLeftwardColumn_cap_eq`). No inverse, moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly
universe u

local instance leftwardVacuumCapInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance leftwardVacuumCapInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (hdot : TruncatedAppendDotNilpotent D (parameterTwist D Sc) cutoff bound) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

/-- The explicit native column `n` of the leftward vacuum cap inverse: the dotted
leftward cup, evaluated by the vacuum sector evaluation and conjugated by the
padded source, corner and cap-target charts. -/
def vacuumLeftwardColumn (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z) (n : ℕ) := by
  subst hZ
  exact (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
        (dc n (.nil _) p₀ ≫ ((P).centralSourceFactorIso i ν₀ ((0, 0) : Sector I)
          (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟨true, trivial⟩).inv) ≫
      ((P).centralSourceCornerIso i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) ⟨true, trivial⟩).inv ≫
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom

include hdot in
/-- **The leftward vacuum cap inverse in the native chart (odd colour).** Leftward
data satisfying the positive inverse equations at the vacuum sector give an
entrywise inverse of the native cap window `[bend; x ^ n ≫ v]_(n < h)` of the
evaluated A6 bend, whose columns are the explicit `vacuumLeftwardColumn`. -/
theorem vacuumLeftwardCapInverse_odd (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
    ∃ j, ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j
        (fun n => vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i Z hZ dc n) := by
  subst hZ
  have hu : ¬StepValid (SKM.up i) false ((0, 0) : Sector I) := by
    simp [StepValid]
  have hd : ¬StepValid (SKM.dn i) true ((0, 0) : Sector I) := by
    simp [StepValid]
  have h₁ := (P).isCapInverse_centralPadded_of_posInverseAt
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HP hu hd
  have h₃ := (h₁.coordinates (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).symm).target
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H)
  have hs : (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedSigma (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hcP hcR hdot) i
        ((0, 0) : Sector I) (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true false ≫
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom =
      ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
        (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) :=
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i
      hdot hP hi)
  have hw : ∀ n : ℕ, (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv ≫
      (P).centralPaddedCap i ((0, 0) : Sector I)
        (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) true n ≫
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom =
      (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ n) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) := fun n =>
    (Iso.inv_comp_eq _).2 (paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP n)
  simp only [Iso.symm_hom, Iso.symm_inv, Category.assoc, hs, hw] at h₃
  exact ⟨_, h₃⟩

/-- **Column moments are bubble entries.** The native column `n` of the leftward
vacuum cap inverse followed by the native cap row `x ^ N ≫ v` is the evaluated left
bubble entry `dcup n ≫ ε xᴺ`, conjugated by the cap-target chart. -/
theorem vacuumLeftwardColumn_cap_eq
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H) ⟶
        ((P).pathFunctor p).obj (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H))
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (n N : ℕ) :
    vacuumLeftwardColumn D Sc m cutoff bound ΛP ΛR hcP hcR H i _ rfl dc n ≫
        (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
        ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
      (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).inv ≫
        (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _)
            (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)) ≫
        (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom := by
  simp only [vacuumLeftwardColumn, Category.assoc]
  rw [← paddedVacuumCap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i hP N,
    (P).map_dcup_epsEntry_eq_padded cc i ν₀ ((0, 0) : Sector I)
      (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
      (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) (dc n (.nil _) p₀) N]
  simp only [Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

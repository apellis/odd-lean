/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumLeftwardMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumCapMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend
import OddMath.QuiverHecke.SwappedVacuum.InverseColumnEvenSeries

/-! # Even moments of the leftward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*,
§8 (the left-bubble series of `AdjunctionBubbleSeries.left_even`).

The even-colour counterpart of `ELVTensorVacuumColumnMoments` and
`ELVTensorVacuumLeftwardMoments`. On the prescribed tensor vacuum at an even
colour, with the actual mate slide (`q = 1`), the probe `(x - 1)^m`, the
reservoir window and the reservoir moments `1/E(-z)`, the decoded moments of a
positive-height inverse column `a` are the coefficients of the substituted
series `E(-w)(1 - w)^(-m)` (`tensorVacuumColumn_even_moments`). Leftward data
satisfying the positive inverse equations at the vacuum sector give such an
inverse whose column products with the native cap rows are the conjugated
evaluated left bubble entries `dcup n ≫ ε xᴺ`
(`vacuumLeftwardCapInverse_even`, `tensorVacuum_leftward_even_moments`).
No inverse, moment or bubble value is assumed. See
`docs/Nondegeneracy/InverseColumnMoments.md`.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction CyclotomicCrossingTensor PowerVacuumCoefficient ProbeVacuumCap
open Finset
universe u

section Generic

variable {I' X' k' : Type u} [AddCommGroup X'] [CommRing k'] {C : Type*} [Category C]
  [Preadditive C] [Linear k' C] {Xo Yo V' : C}

/-- The even inverse-column moment identity for an arbitrary column `a`, read through
an algebra map `ρ` on `End V'`: with the mate slide at `q = 1`, the even probe
`(x - 1)^P`, the two windows and the reservoir series `1/E(-z)`, the column moments
are the substituted-series coefficients. -/
theorem even_column_moments_of_slide (D : SKM.Datum I' X') {R : Type*} [Ring R]
    [Algebra k' R] (φ : MvPolynomial (I' × ℕ) k' →ₐ[k'] R) (ρ : End V' →ₐ[k'] R)
    (P : I' → ℕ) (i : I') (hi : D.parity i = 0) (h N : ℕ) (hh : 0 < h) (hN : 0 < N)
    (hhN : h + N = P i) (x : End Xo) (y : End Yo) (s : Xo ⟶ Yo) (u : V' ⟶ Yo)
    (v : Xo ⟶ V') (ell : Yo ⟶ V') (a : V' ⟶ Xo)
    (hslide : s ≫ y - (1 : k') • (x ≫ s) = v ≫ u) (has : a ≫ s = 0)
    (hprobe : SwappedVacuum.capPolynomial
      (fun n => ((Polynomial.X - 1 : Polynomial k') ^ P i).coeff n) (h + N) x = 0)
    (hcol : ∀ j < h, a ≫ (x ^ j) ≫ v = if j + 1 = h then 𝟙 V' else 0)
    (hwin : ∀ j < N, u ≫ (y ^ j) ≫ ell = if j + 1 = N then 𝟙 V' else 0)
    (hT : PowerSeries.mk (fun l => ρ (u ≫ (y ^ (N - 1 + l)) ≫ ell)) =
      PowerSeries.map φ.toRingHom
        (PowerSeries.invOfUnit (PowerSeries.rescale (-1) (SKM.SYM.generatorSeries k' i)) 1))
    (n : ℕ) :
    ρ (a ≫ (x ^ (h - 1 + n)) ≫ v) = φ (PowerSeries.coeff n
        (VacuumSeries.substitutedSeries k' (SKM.SYM.probeSeries D k' P) i)) := by
  refine SwappedVacuum.even_inverse_column_moments D φ P i hi h N hh hN hhN
    (fun j => ρ (a ≫ (x ^ j) ≫ v)) (fun j => ρ (u ≫ (y ^ j) ≫ ell)) ?_ ?_ ?_ ?_ hT n
  · intro j hj
    simp only [hcol j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro j hj
    simp only [hwin j hj]
    split_ifs
    exacts [map_one ρ, map_zero ρ]
  · intro d
    have h0 := congrArg ρ (SwappedVacuum.column_reservoir_relation (1 : k') (by norm_num)
      x y s u v ell a (h + N) _ hslide has hprobe d)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul, map_sum]
    refine congrArg _ (sum_congr rfl fun j _ => ?_)
    rw [map_smul, ← map_mul, End.mul_def]
  · intro mm
    have h0 := congrArg ρ (SwappedVacuum.column_probe_relation x v a (h + N) _ hprobe mm)
    rw [map_zero, map_sum] at h0
    rw [← h0]
    refine sum_congr rfl fun n _ => ?_
    rw [map_smul]

end Generic

section Tensor

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
  (m : I → ℕ) (cutoff : I → ℕ) (L : I × ℕ → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
local notation "bound" => SKM.SYM.elvPowerWeightBound D cutoff L + 1
local notation "W₀" => Functor.obj (restriction (contentInclusion D Sc cutoff bound (0 : Multiset I)))
  (weightedVacuum D Sc cutoff L)
local notation "H" => VacuumTensor.probeFunctor D Sc m cutoff bound W₀
local notation "R₀" => contentModuleTarget D Sc cutoff bound (0 : Multiset I)
local notation "N₀" => probeOldVacuumRegular D Sc m
local notation "V" => Superfunctor.obj H N₀
local notation "star" => (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc cutoff bound 0)
local notation "AQ" => CoefficientPowerQuotient (k := k) D cutoff L

variable (i : I)
local notation "K" => contentAppend D Sc cutoff bound (0 : Multiset I) [i]

include sy hc in
/-- **Even-colour column moments on the tensor vacuum.** For a column `a`
killed by the actual A6 bend with the column window of height `h`, where
`h + cutoff i = m i`, the decoded column moments `a ≫ x^(h-1+s) ≫ v` are the
coefficients of the substituted series of `AdjunctionBubbleSeries.left_even`. -/
theorem tensorVacuumColumn_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = m i)
    (a : V ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (has : a ≫ evaluatedMixedBend D Sc m cutoff bound i hP H = 0)
    (hcol : ∀ j < h, a ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫ shiftedPreCap D Sc m R₀ i hP H =
      if j + 1 = h then 𝟙 V else 0)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hwin : ∀ j < cutoff i, (adjunction K).unit.app V ≫
      (evaluatedPostDot D Sc m cutoff bound i H ^ j) ≫ tensorPowerVacuumCap D Sc m cutoff L i hN =
      if j + 1 = cutoff i then 𝟙 V else 0 :=
    fun j hj => tensorPowerVacuumCap_window D Sc m cutoff L i hN j hj
  have hmom := even_column_moments_of_slide D (capCoefficientLmul D cutoff L)
    (tensorVacuumEndDecode D Sc m cutoff L) m i hi h (cutoff i) hh hN hhN
    (shiftedPreDot D Sc m R₀ i H)
    (evaluatedPostDot D Sc m cutoff bound i H) (evaluatedMixedBend D Sc m cutoff bound i hP H)
    ((adjunction K).unit.app V) (shiftedPreCap D Sc m R₀ i hP H)
    (tensorPowerVacuumCap D Sc m cutoff L i hN) a
    (evaluatedMixedBend_even_slide_sub D Sc m cutoff L sy hc i hi hP) has
    (by rw [hhN]; exact shiftedPreDot_even_capPolynomial D Sc m cutoff L i hi) hcol hwin
    (tensorVacuum_even_reservoir_series D Sc m cutoff L i hi hN) s
  have e1 := tensorVacuumEndDecode_apply D Sc m cutoff L
    (a ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫ shiftedPreCap D Sc m R₀ i hP H) z
  rw [hmom, capCoefficientLmul_apply] at e1
  exact e1.symm

include sy hc in
/-- **Chosen inverse column, even colour.** If the cap window `[bend; x^n ≫ v]_(n < h)` of
the actual A6 bend has an entrywise inverse `(j, A)`, its last padded column `A (h - 1)` has
the substituted-series moments of `tensorVacuumColumn_even_moments`. -/
theorem tensorVacuumCapInverse_even_moments
    (hi : D.parity i = 0) (hP : 0 < probeCutoff D m i) (hN : 0 < cutoff i)
    (h : ℕ) (hh : 0 < h) (hhN : h + cutoff i = m i)
    (jY : _ ⟶ shiftedPreSourceObject D Sc m R₀ i H)
    (A : Fin h → (V ⟶ shiftedPreSourceObject D Sc m R₀ i H))
    (hA : SwappedAssembly.ProbeWindow.IsCapInverse
      (evaluatedMixedBend D Sc m cutoff bound i hP H)
      (fun n : Fin h => (shiftedPreDot D Sc m R₀ i H ^ (n : ℕ)) ≫ shiftedPreCap D Sc m R₀ i hP H)
      jY A)
    (s : ℕ) (z : (V).obj star) :
    tensorVacuumDecodeLinear D Sc m cutoff L
        ((A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ (h - 1 + s)) ≫
          shiftedPreCap D Sc m R₀ i hP H).total star z) =
      polynomialToPower D cutoff L (PowerSeries.coeff s
          (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
        tensorVacuumDecodeLinear D Sc m cutoff L z := by
  have hcol : ∀ j < h, A ⟨h - 1, by omega⟩ ≫ (shiftedPreDot D Sc m R₀ i H ^ j) ≫
      shiftedPreCap D Sc m R₀ i hP H = if j + 1 = h then 𝟙 V else 0 := by
    intro j hj
    have e := hA.2.2.2.1 ⟨h - 1, by omega⟩ ⟨j, hj⟩
    dsimp only at e
    rw [e]
    by_cases hj' : j + 1 = h
    · have hf : (⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩ := Fin.ext (by dsimp only; omega)
      simp only [hf, hj', ↓reduceIte]
    · have hf : ¬((⟨h - 1, by omega⟩ : Fin h) = ⟨j, hj⟩) := fun e => hj' (by
        rw [Fin.ext_iff] at e; dsimp only at e; omega)
      simp only [hf, hj', ↓reduceIte]
  exact tensorVacuumColumn_even_moments D Sc m cutoff L sy hc i hi hP hN h hh hhN
    (A ⟨h - 1, by omega⟩) (hA.2.1 _) hcol s z

end Tensor

end OddMath.QuiverHecke.ELVOld

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance leftwardEvenMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

omit [Fintype I] in
private instance leftwardEvenMomentsZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D (parameterTwist D Sc) cutoff bound β) :=
  ⟨⟨elvZeroModule D (parameterTwist D Sc) cutoff bound β,
    elvZeroModule_isZero D (parameterTwist D Sc) cutoff bound β⟩⟩

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

include sy hc in
/-- **The leftward vacuum cap inverse in the native chart (even colour).** Leftward
data satisfying the positive inverse equations at the vacuum sector give an
entrywise inverse of the native cap window `[bend; x ^ n ≫ v]_(n < h)` of the
evaluated A6 bend, whose columns are the explicit `vacuumLeftwardColumn`. -/
theorem vacuumLeftwardCapInverse_even (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
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
    (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀ ((0, 0) : Sector I)
    (vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR) lc dc HP hu hd
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
    (Iso.inv_comp_eq _).2 (paddedVacuumDx_even D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi)
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

include sy hc in
/-- **Leftward vacuum cap inverse with bubble-entry columns.** For leftward data
satisfying the positive inverse equations at an input equal to the vacuum sector
input, the native cap window of the evaluated A6 bend has an entrywise inverse
whose column products with the native cap rows `x ^ N ≫ v` are the evaluated left
bubble entries `dcup n ≫ ε xᴺ`, conjugated by one isomorphism `c` (even colour). -/
theorem vacuumLeftwardCapInverse_bubbleEntries_even (Z : (P).H ((0, 0) : Sector I))
    (hZ : Z = vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Z ⟶ ((P).pathFunctor p).obj Z)
    (HP : (P).PosInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Z lc dc)
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 0) :
    ∃ (c : _ ≅ _) (j : _) (A : Fin (D.h i ν₀).toNat → _),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (ProbeVacuumCap.evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i hP
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H))
        (fun n : Fin (D.h i ν₀).toNat => (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ (n : ℕ)) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H)) j A ∧
      ∀ (n : Fin (D.h i ν₀).toNat) (N : ℕ),
        A n ≫ (ProbeVacuumCap.shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
          (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) ^ N) ≫
          ProbeVacuumCap.shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i hP
            (vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR H) =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Z) ≫ c.hom := by
  subst hZ
  obtain ⟨j, hj⟩ := vacuumLeftwardCapInverse_even D Sc m cutoff bound ΛP ΛR hcP hcR H
    sy hc i _ rfl lc dc HP hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H, hj,
    fun n N => vacuumLeftwardColumn_cap_eq D Sc m cutoff bound ΛP ΛR hcP hcR H i dc cc hP
      n N⟩

end Generic

section Tensor

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)
local notation "Zt" => (SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR).obj
local notation "H" => VacuumTensor.probeFunctor D (parameterTwist D Sc) m cutoff bound
  ((BalancedInduction.restriction
    (contentInclusion D (parameterTwist D Sc) cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D (parameterTwist D Sc) cutoff L))
local notation "V" => Superfunctor.obj H (probeOldVacuumRegular D
  (parameterTwist D Sc) m)
local notation "star" =>
  (⟨⟨[]⟩, rfl⟩ : ContentCategory D (parameterTwist D Sc) cutoff bound 0)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

omit [Fintype I] in
private theorem even_probeCutoff' (hi : D.parity i = 0) : probeCutoff D m i = m i := by
  simp [probeCutoff, probeDotExponent, hi]

include sy hc in
/-- **Even moments of the leftward vacuum bubble entries.** For an even colour with
`0 < N_i < P_i` and `h = P_i - N_i`, leftward data satisfying the positive inverse
equations at the tensor vacuum give an entrywise inverse `(j, A)` of the native cap
window of the tensor vacuum bend such that every column product
`A n ≫ x ^ N ≫ v` is the evaluated left bubble entry `dcup n ≫ ε xᴺ` conjugated by
one isomorphism `c`, and the last column has the substituted-series moments: the
shift `h - 1 + s` decodes to multiplication by the `s`-th coefficient of the
substituted probe series. -/
theorem tensorVacuum_leftward_even_moments (hi : D.parity i = 0)
    (hN : 0 < cutoff i) (hlt : cutoff i < probeCutoff D m i)
    (lc : ∀ (_q : SPath (SKM.wd D ν₀ [SKM.dn i, SKM.up i]) ((0, 0) : Sector I)
        ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _q).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (dc : ℕ → ∀ (_r : SPath (SKM.wd D ν₀ []) ((0, 0) : Sector I) ((0, 0) : Sector I))
      (p : SPath (SKM.wd D ν₀ [SKM.up i, SKM.dn i]) ((0, 0) : Sector I) ((0, 0) : Sector I)),
      ((P).pathFunctor _r).obj Zt ⟶ ((P).pathFunctor p).obj Zt)
    (HP : (P).PosInverseAt (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc) i ν₀
      ((0, 0) : Sector I) ((0, 0) : Sector I) Zt lc dc)
    (cc : (P).CrossCoeff) :
    ∃ (c : _ ≅ V) (j : _) (A : Fin (probeCutoff D m i - cutoff i) →
        (V ⟶ shiftedPreSourceObject D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H)),
      (∃ h, c.hom = eqToHom h) ∧ ProbeWindow.IsCapInverse
        (evaluatedMixedBend D (parameterTwist D Sc) m cutoff bound i (hN.trans hlt) H)
        (fun n : Fin (probeCutoff D m i - cutoff i) =>
          (shiftedPreDot D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
              (n : ℕ)) ≫
            shiftedPreCap D (parameterTwist D Sc) m
              (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
              (hN.trans hlt) H) j A ∧
      (∀ (n : Fin (probeCutoff D m i - cutoff i)) (N : ℕ),
        A n ≫ (shiftedPreDot D (parameterTwist D Sc) m
          (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^ N) ≫
          shiftedPreCap D (parameterTwist D Sc) m
            (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
            (hN.trans hlt) H =
        c.inv ≫ (vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR).map
          (dc n (.nil _) p₀ ≫ (P).epsEntry cc i N ν₀ p₀ (.nil _) Zt) ≫ c.hom) ∧
      ∀ (s : ℕ) (z : (V).obj star),
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
                (probeCutoff D m i - cutoff i - 1 + s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z := by
  classical
  have hP : 0 < probeCutoff D m i := hN.trans hlt
  have hlen := SupportedSectors.vacuum_positive_window_length D Sc m cutoff bound ΛP ΛR
    hcP hcR i
  have hex := vacuumLeftwardCapInverse_bubbleEntries_even D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm lc dc HP cc hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  obtain ⟨c, j, A, hceq, hA, hcap⟩ := hex
  have hhN : probeCutoff D m i - cutoff i + cutoff i = m i := by
    rw [← even_probeCutoff' D m i hi]
    omega
  exact ⟨c, j, A, hceq, hA, hcap, fun s z =>
    tensorVacuumCapInverse_even_moments D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hP hN _ (by omega) hhN j A hA s z⟩

end Tensor

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

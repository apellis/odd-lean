/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeLeftwardVacuumCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumCapInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumColumnMoments
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWholeInput

/-! # Odd moments of the leftward vacuum bubble entries

Research issue #345, toward Brundan–Ellis, *Super Kac–Moody 2-categories*, §8.

Leftward data satisfying the positive inverse equations at the vacuum sector give
an explicit cap inverse of the native cap window of the evaluated A6 bend
(`vacuumLeftwardCapInverse_native_odd`), whose column products with the native cap
rows are the conjugated evaluated left bubble entries `dcup n ≫ ε xᴺ`
(`vacuumLeftwardColumn_cap_native`). At the tensor vacuum this inverse is one to
which `tensorVacuumCapInverse_odd_moments` applies, so the conjugated evaluated
left bubble entries `dcup (h - 1) ≫ ε x^(h - 1 + 2s)` and `dcup (h - 1) ≫ ε x^(h + 2s)`
are the columns with the substituted-series moments
(`tensorVacuum_leftward_odd_moments`). No inverse,
moment or bubble value is assumed.
-/

noncomputable section
set_option quotPrecheck false
open CategoryTheory StringDiagrams Supercategory BicategoryStruct

namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly ProbeVacuumCap PowerVacuumCoefficient
universe u

local instance leftwardVacuumMomentsHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

section Pullback

/-- The return isomorphism of a pulled-back input is an `eqToHom`. -/
theorem capPullbackSelfIso_hom {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
    [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
    [∀ a b : B, PiSupercategory k (a ⟶ b)]
    {I X : Type*} [AddCommGroup X] {D : SKM.Datum I X}
    (T W : SKM.RouquierFamily (k := k) (B := B) D)
    {a a' b b' : X} (ha : a = a') (hb : b = b')
    (Z' : SKM.homWeightSector T.obj W.obj a' b') :
    (capPullbackSelfIso T W ha hb Z').hom = eqToHom (by subst a' b'; rfl) := by
  subst a' b'
  rfl

end Pullback

section Generic

variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)

local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "ν₀" => (P).wt ((0, 0) : Sector I)

variable (H : ProbeVacuumCap.modulePiCategory D (parameterTwist D Sc) m ⟶
  elvWeightSpace D (parameterTwist D Sc) cutoff bound ΛR (-ΛR))
variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "p₀" => SPath.centralUpDn i (SKM.wt D ν₀ [SKM.dn i]) ν₀ ((0, 0) : Sector I)
  ⟨true, trivial⟩

/-- The cap target comparison `paddedVacuumCapTargetIso` is an `eqToHom`. -/
theorem paddedVacuumCapTargetIso_hom_eq_eqToHom :
    ∃ h, (paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H).hom = eqToHom h := by
  rw [paddedVacuumCapTargetIso, Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom,
    capPullbackSelfIso_hom, eqToIso.hom, eqToHom_map, eqToHom_map, eqToHom_trans]
  exact ⟨_, rfl⟩

include sy hc in
/-- **Leftward vacuum cap inverse with bubble-entry columns.** For leftward data
satisfying the positive inverse equations at an input equal to the vacuum sector
input, the native cap window of the evaluated A6 bend has an entrywise inverse
whose column products with the native cap rows `x ^ N ≫ v` are the evaluated left
bubble entries `dcup n ≫ ε xᴺ`, conjugated by one isomorphism `c`. -/
theorem vacuumLeftwardCapInverse_bubbleEntries (Z : (P).H ((0, 0) : Sector I))
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
    (cc : (P).CrossCoeff) (hP : 0 < probeCutoff D m i) (hi : D.parity i = 1) :
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
  obtain ⟨j, hj⟩ := vacuumLeftwardCapInverse_native_odd D Sc m cutoff bound ΛP ΛR hcP hcR H
    sy hc i _ rfl lc dc HP hP hi
  exact ⟨paddedVacuumCapTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H, j, _,
    paddedVacuumCapTargetIso_hom_eq_eqToHom D Sc m cutoff bound ΛP ΛR hcP hcR H, hj,
    fun n N => vacuumLeftwardColumn_cap_native D Sc m cutoff bound ΛP ΛR hcP hcR H i dc cc hP
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
private theorem odd_probeCutoff' (hi : D.parity i = 1) : probeCutoff D m i = 2 * m i := by
  simp [probeCutoff, probeDotExponent, hi]

include sy hc in
/-- **Odd moments of the leftward vacuum bubble entries.** For an odd colour with
`0 < N_i < P_i` and `h = P_i - N_i`, leftward data satisfying the positive inverse
equations at the tensor vacuum give an entrywise inverse `(j, A)` of the native cap
window of the tensor vacuum bend such that every column product
`A n ≫ x ^ N ≫ v` is the evaluated left bubble entry `dcup n ≫ ε xᴺ` conjugated by
one isomorphism `c`, and the last column has the substituted-series moments: the
shift `h - 1 + 2s` decodes to multiplication by the `s`-th coefficient of the
substituted probe series and the shift `h + 2s` to that coefficient times the
reservoir odd coefficient. -/
theorem tensorVacuum_leftward_odd_moments (hi : D.parity i = 1)
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
                (probeCutoff D m i - cutoff i - 1 + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
            tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z ∧
        tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L
            ((A ⟨probeCutoff D m i - cutoff i - 1, by omega⟩ ≫
              (shiftedPreDot D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i H ^
                (probeCutoff D m i - cutoff i + 2 * s)) ≫
              shiftedPreCap D (parameterTwist D Sc) m
                (contentModuleTarget D (parameterTwist D Sc) cutoff bound (0 : Multiset I)) i
                (hN.trans hlt) H).total star z) =
          ((-1 : k) ^ (cutoff i + 1) •
              coefficientPowerQuotientMap D cutoff L (SKM.SYM.delta D k ⟨i, hi⟩)) *
            (polynomialToPower D cutoff L (PowerSeries.coeff s
              (VacuumSeries.substitutedSeries k (SKM.SYM.probeSeries D k m) i)) *
              tensorVacuumDecodeLinear D (parameterTwist D Sc) m cutoff L z) := by
  classical
  have hP : 0 < probeCutoff D m i := hN.trans hlt
  have hlen := SupportedSectors.vacuum_positive_window_length D Sc m cutoff bound ΛP ΛR
    hcP hcR i
  have hex := vacuumLeftwardCapInverse_bubbleEntries D Sc m cutoff bound ΛP ΛR hcP hcR
    (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) sy hc i Zt
    (tensorSectorInput_eq_supported D Sc m cutoff L ΛR ΛP hcP hcR).symm lc dc HP cc hP hi
  rw [show vacuumBendBlock D (parameterTwist D Sc) m cutoff bound ΛR
      (tensorOutputAt D (parameterTwist D Sc) m cutoff L ΛR) = H from
    tensorOutputAt_empty D (parameterTwist D Sc) m cutoff L ΛR, hlen] at hex
  obtain ⟨c, j, A, hceq, hA, hcap⟩ := hex
  have hhN : probeCutoff D m i - cutoff i + cutoff i = 2 * m i := by
    rw [← odd_probeCutoff' D m i hi]
    omega
  exact ⟨c, j, A, hceq, hA, hcap, fun s z =>
    tensorVacuumCapInverse_odd_moments D (parameterTwist D Sc) m cutoff L sy
      (parameterTwist_homogeneous D Sc hc) i hi hP hN _ (by omega) hhN j A hA s z⟩

end Tensor

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

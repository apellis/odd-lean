import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalFactor
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedVacuumBend
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumPrincipalCap

/-! # The actual principal inverse and the normalized tensor-vacuum cap

SwappedVacuumNonpositiveBubbles §4: the chosen supported-vacuum principal
inverse, evaluated at the regular probe, gives the polynomial cap at
equal positive levels. Its first closure acts on every coefficient
vector as minus the original odd exterior generator.
-/
noncomputable section
set_option quotPrecheck false
set_option autoImplicit false
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open BalancedInduction CyclotomicAction SwappedAssembly SKM ProbeVacuumCap
universe u
local instance principalInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "H" => tensorOutputAt D Sc' m cutoff L ΛR
local notation "Z" => vacuumSectorInput D Sc m cutoff bound ΛP ΛR hcP hcR H
local notation "E" => vacuumSectorEvaluation D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "R₀" => contentModuleTarget D Sc' cutoff bound (0 : Multiset I)
local notation "H₀" => VacuumTensor.probeFunctor D Sc' m cutoff bound
  ((restriction (contentInclusion D Sc' cutoff bound (0 : Multiset I))).obj
    (PowerVacuumCoefficient.weightedVacuum D Sc' cutoff L))
local notation "N₀" => probeOldVacuumRegular D Sc' m
local notation "V" => (H₀).obj N₀

private instance principalInverseZero (β : Multiset I) :
    Limits.HasZeroObject (ContentModules D Sc' cutoff bound β) :=
  ⟨⟨elvZeroModule D Sc' cutoff bound β, elvZeroModule_isZero D Sc' cutoff bound β⟩⟩

/-- Output projection and total regular-probe evaluation give precisely
the evaluation used in the prescribed padded bend chart. -/
theorem tensorVacuumEvaluation_eq : E =
    SupportedSectors.reservoirOutputEval D Sc m cutoff bound ΛP ΛR hcP hcR (0,0)
      (sectorEmpty D Sc m cutoff bound ΛP ΛR hcP hcR) ⋙
        homTotalEvaluation (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR) := by
  rw [vacuumSectorEvaluation_eq]
  rfl

private theorem mappedPaddedSigma_isIso
    {C C' : Type*} [Category C] [Category C'] [Preadditive C'] [Limits.HasZeroObject C']
    (t : Sector I) (A : (P).H t) (E₁ : (P).H t ⥤ C) (Q : C ⥤ C')
    (cc : (P).CrossCoeff) (j : I) (a b : Bool)
    (ha : StepValid (up j) a t) (hb : StepValid (dn j) b t)
    (hI : IsIso (E₁.map ((P).centralFactorSigma cc j t A ⟨a, ha⟩ ⟨b, hb⟩))) :
    IsIso ((P).centralPaddedSigma cc j t A (E₁ ⋙ Q) a b) := by
  let := hI
  simp only [ProbeReservoir.centralPaddedSigma, dite_eq_left ha, dite_eq_left hb,
    Functor.comp_map]
  infer_instance

variable (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "c" => elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc

/-- Evaluation preserves the actual chosen principal isomorphism.
The whole-output inverse is constructed by `vacuumPrincipalIso`. -/
theorem tensorPaddedPrincipal_isIso (hlevel : probeCutoff D m i = cutoff i) :
    IsIso ((P).centralPaddedSigma c i (0,0) Z E true false) := by
  change IsIso ((P).centralPaddedSigma c i (0,0)
    (tensorSectorInput D Sc m cutoff L ΛR ΛP hcP hcR) E true false)
  rw [tensorSectorInput_eq_supported, tensorVacuumEvaluation_eq]
  let E₁ := SupportedSectors.reservoirOutputEval D Sc m cutoff bound ΛP ΛR hcP hcR (0,0)
    (tensorSectorEmpty D Sc m cutoff L ΛP ΛR hcP hcR)
  let Q := homTotalEvaluation (k := k) (B := ContentModules D Sc' cutoff bound 0)
    (sectorRegular D Sc m cutoff bound ΛP ΛR hcP hcR)
  let W := SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR
  have hI : IsIso (E₁.map ((P).centralFactorSigma c i (0,0) W.obj
      ⟨true, by trivial⟩ ⟨false, by trivial⟩)) := by
    rw [← tensorVacuumPrincipalFactorIso_hom D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel]
    infer_instance
  exact mappedPaddedSigma_isIso D Sc m cutoff L ΛP ΛR hcP hcR (0,0) W.obj E₁ Q c i true false
    (by trivial) (by trivial) hI

/-- At equal positive levels the given native bend is invertible, by
the chosen augmented inverse and the proved padded-bend square. -/
theorem tensorVacuumPrincipalBend_isIso
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hcut : cutoff i = 2 * m i) :
    IsIso (evaluatedMixedBend D Sc' m cutoff bound i hP H₀) := by
  have hlevel : probeCutoff D m i = cutoff i := by
    simpa only [probeCutoff, probeDotExponent, hi, ite_true] using hcut.symm
  let := tensorPaddedPrincipal_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel
  have hA := paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi
  rw [show vacuumBendBlock D Sc' m cutoff bound ΛR H = H₀ from
    tensorOutputAt_empty D Sc' m cutoff L ΛR] at hA
  let S := paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i
  let T := paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i
  have hs : S.inv ≫ (P).centralPaddedSigma c i (0,0) Z E true false ≫ T.hom =
      evaluatedMixedBend D Sc' m cutoff bound i hP H₀ := by
    rw [Category.assoc, hA, Iso.inv_hom_id_assoc]
  rw [← hs]
  infer_instance

/-- The inverse square retains the prescribed padded entry and both
native source and target charts; the principal row is not replaced by
an independently assumed inverse. -/
theorem tensorVacuumPrincipalBend_inverse_square
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hcut : cutoff i = 2 * m i) :
    let hlevel : probeCutoff D m i = cutoff i := by
      simpa only [probeCutoff, probeDotExponent, hi, ite_true] using hcut.symm
    let _ := tensorPaddedPrincipal_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel
    let _ := tensorVacuumPrincipalBend_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
    inv ((P).centralPaddedSigma c i (0,0) Z E true false) =
      (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).hom ≫
        inv (evaluatedMixedBend D Sc' m cutoff bound i hP H₀) ≫
        (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i).inv := by
  dsimp only
  have hlevel : probeCutoff D m i = cutoff i := by
    simpa only [probeCutoff, probeDotExponent, hi, ite_true] using hcut.symm
  let := tensorPaddedPrincipal_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel
  let := tensorVacuumPrincipalBend_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
  have hA := paddedVacuumDx_odd D Sc m cutoff bound ΛP ΛR hcP hcR H i sy hc hP hi
  rw [show vacuumBendBlock D Sc' m cutoff bound ΛR H = H₀ from
    tensorOutputAt_empty D Sc' m cutoff L ΛR] at hA
  exact ProbeWindow.inverse_of_chart_square
    (paddedVacuumSourceIso D Sc m cutoff bound ΛP ΛR hcP hcR H i)
    (paddedVacuumTargetIso D Sc m cutoff bound ΛP ΛR hcP hcR H i)
    (evaluatedMixedBend D Sc' m cutoff bound i hP H₀)
    ((P).centralPaddedSigma c i (0,0) Z E true false) hA.symm

/-- The actual native principal inverse followed by the prescribed normalized pre-cap. -/
def tensorVacuumPrincipalCap
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hcut : cutoff i = 2 * m i) :
    (restriction (contentAppend D Sc' cutoff bound (0 : Multiset I) [i])).obj
      ((induction (contentAppend D Sc' cutoff bound (0 : Multiset I) [i])).obj V) ⟶ V :=
  letI := tensorVacuumPrincipalBend_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
  inv (evaluatedMixedBend D Sc' m cutoff bound i hP H₀) ≫
    shiftedPreCap D Sc' m R₀ i hP H₀

/-- The inverse cap is the native polynomial cap, with no additional
bend, cap, inverse-window or moment hypothesis. -/
theorem tensorVacuumPrincipalCap_eq_polynomial
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hN : 0 < cutoff i) (hcut : cutoff i = 2 * m i) :
    tensorVacuumPrincipalCap D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut =
      PowerVacuumCoefficient.tensorPolynomialCap D Sc' m cutoff L i hN (m i) := by
  let := tensorVacuumPrincipalBend_isIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut
  have h := evaluatedMixedBend_polynomialCap_eq_preCap D Sc' m cutoff L sy
    (parameterTwist_homogeneous D Sc hc) i hi hP hN hcut.symm
  dsimp only [tensorVacuumPrincipalCap]
  rw [← h, IsIso.inv_hom_id_assoc]
  unfold PowerVacuumCoefficient.tensorPolynomialCap
  with_unfolding_all rfl

/-- The normalized odd principal closure uses the literal native reservoir unit. -/
def tensorVacuumPrincipalClosure
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hcut : cutoff i = 2 * m i) : End V :=
  unitDotColumn (contentAppend D Sc' cutoff bound (0 : Multiset I) [i])
    (canonicalAppendDot_supernatural D Sc' cutoff bound (0 : Multiset I) i) V 0 ≫
      tensorVacuumPrincipalCap D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut

/-- On every input vector the actual inverse closure is multiplication
by minus the original independent odd coefficient. -/
theorem tensorVacuumPrincipalClosure_decode
    (hi : D.parity i = 1) (hP : 0 < probeCutoff D m i)
    (hN : 0 < cutoff i) (hcut : cutoff i = 2 * m i)
    (z : (V).obj (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc' cutoff bound 0)) :
    PowerVacuumCoefficient.tensorVacuumDecodeLinear D Sc' m cutoff L
      ((tensorVacuumPrincipalClosure D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hi hP hcut).total
        (⟨⟨[]⟩, rfl⟩ : ContentCategory D Sc' cutoff bound 0) z) =
      -(coefficientPowerQuotientMap D cutoff L (SYM.delta D k ⟨i, hi⟩)) *
        PowerVacuumCoefficient.tensorVacuumDecodeLinear D Sc' m cutoff L z := by
  unfold tensorVacuumPrincipalClosure
  rw [tensorVacuumPrincipalCap_eq_polynomial D Sc m cutoff L ΛP ΛR hcP hcR sy hc i
    hi hP hN hcut]
  with_unfolding_all exact PowerVacuumCoefficient.tensorPolynomialCap_zero_height_odd D Sc' m cutoff L i
    hi hN (m i) hcut z

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum

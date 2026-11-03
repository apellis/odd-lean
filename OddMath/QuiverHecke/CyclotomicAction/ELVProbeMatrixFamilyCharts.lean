import OddMath.QuiverHecke.CyclotomicAction.ELVProbeMatrixCharts
import OddMath.QuiverHecke.CyclotomicAction.ELVInductionGridMatrixFamilies

/-! # Genuine scalar charts on the prescribed finite parity families

DeformedMatrixComparison (4), (5) compares the entire finite families of
actual shifted module values. Each slot uses its selected E/F, F/E or value
chart conjugated by the given module parity coordinates. No matrix inverse
or compatibility premise is used to construct these invertible charts.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld OddMath.QuiverHecke.ELVOld.BalancedInduction
namespace OddMath.QuiverHecke
universe u

private theorem familyChartEqIso_mem
    {k A : Type u} [CommRing k] [Category.{u} A] [Preadditive A] [Linear k A]
    [Supercategory k A] {F G : Superfunctor k A (SVec k)} (h : F = G) :
    (eqToIso h).hom ∈ parity (R := k) _ _ 0 := by
  cases h
  exact id_mem F

private theorem familyChart_total_mem
    {k A : Type u} [CommRing k] [Category.{u} A] [Preadditive A] [Linear k A]
    [Supercategory k A] {F G : Superfunctor k A (SVec k)} {f : F ⟶ G}
    (hf : f ∈ parity (R := k) _ _ 0) (w : A) :
    f.total w ∈ parity (R := k) (F.obj w) (G.obj w) 0 := by
  have hz := Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) w
  rw [SuperNatTrans.total, hz, add_zero]
  exact f.app_mem 0 w

private theorem familyPiChart_mem
    {k : Type u} {ι : Type} [CommRing k] (V W : ι → SVec k)
    (e : ∀ a, V a ≃ₗ[k] W a)
    (he : ∀ a, SVec.ofHom (e a).toLinearMap ∈ parity (R := k) (V a) (W a) 0) :
    SVec.ofHom (LinearEquiv.piCongrRight e).toLinearMap ∈
      parity (R := k) (OddMath.FiniteSuperspace.product V) (OddMath.FiniteSuperspace.product W) 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  rw [add_zero, OddMath.FiniteSuperspace.mem_product_part]
  intro a
  change e a (x a) ∈ (W a).part q
  simpa only [add_zero, SVec.ofHom_apply, LinearEquiv.coe_coe]
    using SVec.apply_mem_part (he a)
    ((OddMath.FiniteSuperspace.mem_product_part V q x).mp hx a)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELVOld.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELVOld.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "S" => probeOrdinaryAppend D Sc m (i :: ν) i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "RN" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)
local instance scalarFamilyOldPi : PiSupercategory k
    (Superfunctor k (ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarFamilyOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory

/-- The original scalar value equality, oriented from old to ordinary values. -/
def probeMatrixValueLinearEquiv
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    N.obj w ≃ₗ[k] (O).obj ((U).obj w) := (moduleIsoLinearEquiv e w).symm

theorem probeMatrixValueLinearEquiv_mem
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeMatrixValueLinearEquiv D Sc m ν i N hN w).toLinearMap ∈
      parity (R := k) (N.obj w) ((O).obj ((U).obj w)) 0 :=
  familyChart_total_mem (inv_mem e
    (familyChartEqIso_mem (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN))) w

/-- The inverse value chart is the original identity-on-vectors scalar comparison. -/
theorem probeMatrixValueLinearEquiv_symm_apply
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
    (b : (O).obj ((U).obj w)) :
    (probeMatrixValueLinearEquiv D Sc m ν i N hN w).symm b = b := by
  change probeCapValueLinear D Sc m ν i N hN w b = b
  exact probeCapValueLinear_apply D Sc m ν i N hN w b

/-- The selected forward value chart also keeps every original module vector. -/
theorem probeMatrixValueLinearEquiv_apply
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (b : N.obj w) :
    probeMatrixValueLinearEquiv D Sc m ν i N hN w b = b := by
  have h := (probeMatrixValueLinearEquiv D Sc m ν i N hN w).apply_symm_apply b
  have hv := probeMatrixValueLinearEquiv_symm_apply D Sc m ν i N hN w b
  exact (congrArg (probeMatrixValueLinearEquiv D Sc m ν i N hN w) hv).symm.trans h

/-- The selected E/F source chart is even on its actual module value spaces. -/
theorem probeMatrixSourceLinearEquiv_mem
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeMatrixSourceLinearEquiv D Sc m ν i N hN w).toLinearMap ∈
      parity (R := k) ((induced J RN).obj w)
        ((induced T ((restriction T).obj O)).obj ((U).obj w)) 0 :=
  probeMappedAppendLinearEquiv_mem D Sc m ν RN hR ((restriction T).obj O) c i
    (familyChartEqIso_mem (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)) w

/-- The selected F/E target chart is even on its actual module value spaces. -/
theorem probeMatrixTargetLinearEquiv_mem
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeMatrixTargetLinearEquiv D Sc m ν i N hN w).toLinearMap ∈
      parity (R := k) (((restriction K).obj (induced K N)).obj w)
        (((restriction S).obj (induced S O)).obj ((U).obj w)) 0 :=
  probeAppendLinearEquiv_mem D Sc m (i :: ν) N hN i ((K).obj w)

/-- Slot charts for the full prescribed finite unit source family. -/
def probeUnitMatrixSlotLinearEquiv (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    (gridUnitMatrixFamily J (D.parity i) N b a).obj w ≃ₗ[k]
      (gridUnitMatrixFamily T (D.parity i) O b a).obj ((U).obj w) :=
  match a with
  | none => shiftedModuleValueLinearEquiv (induced J RN) (induced T ((restriction T).obj O))
      w ((U).obj w) (probeMatrixSourceLinearEquiv D Sc m ν i N hN w) (D.parity i)
  | some r => shiftedModuleValueLinearEquiv N O w ((U).obj w)
      (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)

/-- Slot charts for the full prescribed finite cap target family. -/
def probeCapMatrixSlotLinearEquiv (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    (gridCapMatrixFamily K (D.parity i) N b a).obj w ≃ₗ[k]
      (gridCapMatrixFamily S (D.parity i) O b a).obj ((U).obj w) :=
  match a with
  | none => shiftedModuleValueLinearEquiv ((restriction K).obj (induced K N))
      ((restriction S).obj (induced S O)) w ((U).obj w)
      (probeMatrixTargetLinearEquiv D Sc m ν i N hN w) (D.parity i)
  | some r => shiftedModuleValueLinearEquiv N O w ((U).obj w)
      (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)

/-- Every selected shifted unit-source slot chart is even. -/
theorem probeUnitMatrixSlotLinearEquiv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    SVec.ofHom (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w a).toLinearMap ∈
      parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    exact shiftedModuleValueLinearEquiv_hom_mem (induced J RN) (induced T ((restriction T).obj O))
      w ((U).obj w) (probeMatrixSourceLinearEquiv D Sc m ν i N hN w) (D.parity i)
      (probeMatrixSourceLinearEquiv_mem D Sc m ν i N hN w)
  | some r =>
    exact shiftedModuleValueLinearEquiv_hom_mem N O w ((U).obj w)
      (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)
      (probeMatrixValueLinearEquiv_mem D Sc m ν i N hN w)

/-- Every selected shifted cap-target slot chart is even. -/
theorem probeCapMatrixSlotLinearEquiv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (a : Option (Fin b)) :
    SVec.ofHom (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w a).toLinearMap ∈
      parity (R := k) _ _ 0 := by
  cases a with
  | none =>
    exact shiftedModuleValueLinearEquiv_hom_mem ((restriction K).obj (induced K N))
      ((restriction S).obj (induced S O)) w ((U).obj w)
      (probeMatrixTargetLinearEquiv D Sc m ν i N hN w) (D.parity i)
      (probeMatrixTargetLinearEquiv_mem D Sc m ν i N hN w)
  | some r =>
    exact shiftedModuleValueLinearEquiv_hom_mem N O w ((U).obj w)
      (probeMatrixValueLinearEquiv D Sc m ν i N hN w) (r.val • D.parity i)
      (probeMatrixValueLinearEquiv_mem D Sc m ν i N hN w)

/-- Genuine invertible chart on the entire prescribed shifted unit source. -/
def probeUnitMatrixFamilyLinearEquiv (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    gridUnitMatrixSourceSpace J (D.parity i) N b w ≃ₗ[k]
      gridUnitMatrixSourceSpace T (D.parity i) O b ((U).obj w) :=
  LinearEquiv.piCongrRight (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w)

/-- Genuine invertible chart on the entire prescribed shifted cap target. -/
def probeCapMatrixFamilyLinearEquiv (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    gridCapMatrixTargetSpace K (D.parity i) N b w ≃ₗ[k]
      gridCapMatrixTargetSpace S (D.parity i) O b ((U).obj w) :=
  LinearEquiv.piCongrRight (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w)

/-- The full selected shifted unit-family chart is even. -/
theorem probeUnitMatrixFamilyLinearEquiv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN b w).toLinearMap ∈
      parity (R := k) _ _ 0 :=
  familyPiChart_mem _ _ (probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w)
    (probeUnitMatrixSlotLinearEquiv_mem D Sc m ν i N hN b w)

/-- The full selected shifted cap-family chart is even. -/
theorem probeCapMatrixFamilyLinearEquiv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN b w).toLinearMap ∈
      parity (R := k) _ _ 0 :=
  familyPiChart_mem _ _ (probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w)
    (probeCapMatrixSlotLinearEquiv_mem D Sc m ν i N hN b w)

/-- The full unit chart acts by exactly its prescribed slot charts. -/
theorem probeUnitMatrixFamilyLinearEquiv_apply (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
    (x : gridUnitMatrixSourceSpace J (D.parity i) N b w) (a : Option (Fin b)) :
    probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN b w x a =
      probeUnitMatrixSlotLinearEquiv D Sc m ν i N hN b w a (x a) := rfl

/-- The full cap chart acts by exactly its prescribed slot charts. -/
theorem probeCapMatrixFamilyLinearEquiv_apply (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν))
    (x : gridCapMatrixTargetSpace K (D.parity i) N b w) (a : Option (Fin b)) :
    probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN b w x a =
      probeCapMatrixSlotLinearEquiv D Sc m ν i N hN b w a (x a) := rfl

/-- The inverse selected unit-family chart is even on the same actual gradings. -/
theorem probeUnitMatrixFamilyLinearEquiv_inv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN b w).symm.toLinearMap ∈
      parity (R := k) _ _ 0 :=
  inv_mem (SVec.isoOfLinearEquiv (probeUnitMatrixFamilyLinearEquiv D Sc m ν i N hN b w))
    (probeUnitMatrixFamilyLinearEquiv_mem D Sc m ν i N hN b w)

/-- The inverse selected cap-family chart is even on the same actual gradings. -/
theorem probeCapMatrixFamilyLinearEquiv_inv_mem (b : ℕ)
    (w : ELVOld.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    SVec.ofHom (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN b w).symm.toLinearMap ∈
      parity (R := k) _ _ 0 :=
  inv_mem (SVec.isoOfLinearEquiv (probeCapMatrixFamilyLinearEquiv D Sc m ν i N hN b w))
    (probeCapMatrixFamilyLinearEquiv_mem D Sc m ν i N hN b w)

end OddMath.QuiverHecke

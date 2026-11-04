import OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuumCoefficientClass
import OddMath.QuiverHecke.UpwardPBWCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.SupportedTensorVacuumCoefficientClass
local instance tensorHomPi (A C : PiSCat.{0,0,1} ℚ) : PiSupercategory ℚ (A ⟶ C) :=
  PiTwoSupercategory.homPiLeft A C
private def collisionDatum : SKM.Datum Bool (Bool → ℤ) where
  cd :=
    { root := fun j i => if i = j then 2 else -2
      coroot := fun i => LinearMap.proj i
      coroot_root_self := fun i => by simp }
  isGCM :=
    { diag := fun i => by simp [CartanDatum.cartanMatrix_apply]
      offDiag_nonpos := fun i j h => by simp [CartanDatum.cartanMatrix_apply, h]
      zero_comm := fun i j => by simp [CartanDatum.cartanMatrix_apply, eq_comm] }
  parity := fun _ => 1
  even_of_odd := by
    intro i j _
    change Even (if i = j then (2 : ℤ) else -2)
    split
    · exact ⟨1, by norm_num⟩
    · exact ⟨-1, by norm_num⟩

private def collisionScalars : SKM.Scalars collisionDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)


private abbrev D := collisionDatum
private abbrev originalSc := collisionScalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 20
private def m (_ : Bool) : ℕ := 10
private def Λ : Bool → ℤ := fun _ => 20
private abbrev N := PowerWordContent.powerBound D cutoff L
private def labels : List (Col Bool (Bool → ℤ)) := wd D (Λ - Λ) [up true,up false]
private theorem upward : ∀ a ∈ labels, a.l.1 = true := by simp [labels,wd]
private def path := SPath.reservoirPath labels upward 0
private abbrev ν : List Bool := [false,true]
private abbrev σ : List Bool := ν.reverse
private theorem powers_high (q : Bool × ℕ) : 16 ≤ L q * SKM.SYM.elementaryWeight D q := by
  have hw : 0 < SKM.SYM.elementaryWeight D q := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  change 16 ≤ 20 * SKM.SYM.elementaryWeight D q
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([],1),by simp,by simp,?_⟩
  simp only [List.map_nil,hc,cw,List.reverse_nil,List.nil_append,pl,QuiverHecke.SChain]

private def delta : SYM D ℚ := SYM.delta D ℚ ⟨false,rfl⟩
private theorem inverse_product : (1 - delta) * (1 + delta) = 1 := by
  have hd : delta * delta = 0 := by
    simpa only [delta,pow_two] using SYM.delta_sq D ℚ ⟨false,rfl⟩
  calc
    (1 - delta) * (1 + delta) = (1 + delta) - (delta + delta * delta) := by
      rw [sub_mul,one_mul,mul_add,mul_one]
    _ = 1 := by simp only [hd,add_zero,add_sub_cancel_right]
private theorem mixed_ne_zero : (1 + delta : SYM D ℚ) ≠ 0 := by
  intro hz
  have h := inverse_product
  rw [hz,mul_zero] at h
  have hone : (1 : SYM D ℚ) ≠ 0 := by
    rw [SYM.one_eq_coefficientBasis]
    exact (SYM.coefficientBasis D ℚ).ne_zero _
  exact hone h.symm

private theorem identityNF_value : identityNF.nf (D := D) (Sc := originalSc) = 𝟙 _ := by
  have hc : Categorification.TypeA.canWord σ.length (1 : Equiv.Perm (Fin σ.length)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  simp only [NFIdx.nf,identityNF,hc,List.map_nil,List.nil_append,cw,List.reverse_nil,
    OddMath.QuiverHecke.cl_nil]

private def emptyIndex : SYM.CoefficientIndex D := (0,∅)
private def deltaIndex : SYM.CoefficientIndex D := (0,{⟨false,rfl⟩})
private def unitWindow : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (emptyIndex,identityNF),
    Submodule.subset_span ⟨(emptyIndex,identityNF),by decide,rfl⟩⟩
private def deltaWindow : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (deltaIndex,identityNF),
    Submodule.subset_span ⟨(deltaIndex,identityNF),by decide,rfl⟩⟩
private def mixedWindow : ExtendedAtMost D originalSc σ σ 2 := unitWindow + deltaWindow
private theorem mixedWindow_value :
    mixedWindow.val = sourceCoefficientHom D originalSc (1 + delta) identityNF.nf := by
  change extensionBasis D originalSc σ σ (emptyIndex,identityNF) +
    extensionBasis D originalSc σ σ (deltaIndex,identityNF) = _
  rw [extensionBasis_apply,extensionBasis_apply,sourceCoefficientHom_add_left]
  change sourceCoefficientHom D originalSc (SYM.coefficientBasis D ℚ (0,∅)) identityNF.nf +
    sourceCoefficientHom D originalSc (SYM.coefficientBasis D ℚ (0,{⟨false,rfl⟩})) identityNF.nf = _
  rw [← SYM.one_eq_coefficientBasis, ← SYM.delta_eq_coefficientBasis]
  rfl
private theorem mixedWindow_ne_zero : mixedWindow.val ≠ 0 := by
  intro hz
  rw [mixedWindow_value] at hz
  have h := congrArg (coefficientPBWCoordinate D originalSc identityNF) hz
  rw [coefficientPBWCoordinate_source,map_zero] at h
  exact mixed_ne_zero (by simpa using h)

/-- The concrete mixed coefficient has a nonzero source quotient class;
this detects the coefficient itself in the bounded window. -/
private theorem mixed_class_ne_zero :
    (PowerWordQuotientCoordinates.kernel D originalSc cutoff L σ σ).mkQ
      (sourceCoefficientHom D originalSc (1 + delta) (𝟙 _)) ≠ 0 := by
  intro hz
  have hv := congrArg (PowerWordQuotientCoordinates.quotientEquiv D originalSc cutoff L σ σ) hz
  rw [PowerWordQuotientCoordinates.quotientEquiv_mk,map_zero] at hv
  have hh : mixedWindow = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ mixedWindow.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    rw [mixedWindow_value,identityNF_value]
    exact hv.trans (map_zero _).symm
  exact mixedWindow_ne_zero (congrArg Subtype.val hh)

example : (PowerWordQuotientCoordinates.kernel D originalSc cutoff L σ σ).mkQ
    (sourceCoefficientHom D originalSc (1 + delta) (𝟙 _)) ≠ 0 := mixed_class_ne_zero

private theorem probePairing (i : Bool) : (probeCutoff D m i : ℤ) = D.h i Λ := by
  cases i <;> norm_num [probeCutoff,probeDotExponent,m,D,collisionDatum,SKM.Datum.h,Λ]
private theorem reservoirPairing (i : Bool) : (cutoff i : ℤ) = D.h i Λ := rfl
private abbrev vacuum := SupportedSectors.tensorMatrixVacuum D originalSc m cutoff Λ Λ L σ
private abbrev action := SupportedSectors.tensorMatrixCoefficientAction D originalSc m cutoff Λ Λ L σ
  (SKM.ob D (Λ - Λ) (upWord σ))
private abbrev observe := SupportedSectors.tensorWordQuotientObservation D originalSc cutoff L m Λ Λ
  probePairing reservoirPairing σ σ (SupportedSectors.tensorSourcePath D Λ Λ σ)

/-- The theorem is applied to the literal nonempty two-odd tensor matrix
vacuum and the concrete full mixed coefficient whose quotient class is nonzero. -/
example : observe (action (1 + delta) vacuum) =
    (PowerWordQuotientCoordinates.kernel D originalSc cutoff L σ σ).mkQ
      (sourceCoefficientHom D originalSc (1 + delta) (𝟙 _)) :=
  SupportedSectors.tensorWordQuotientObservation_coefficient_vacuum D originalSc cutoff L m Λ Λ
    probePairing reservoirPairing σ (1 + delta)

example : observe (action (1 + delta) vacuum) ≠ 0 := by
  rw [SupportedSectors.tensorWordQuotientObservation_coefficient_vacuum]
  exact mixed_class_ne_zero

example : action (1 + delta) vacuum ≠ 0 := by
  intro hz
  have h : observe (action (1 + delta) vacuum) ≠ 0 := by
    rw [SupportedSectors.tensorWordQuotientObservation_coefficient_vacuum]
    exact mixed_class_ne_zero
  rw [hz,map_zero] at h
  exact h rfl

end NonVacuity.SupportedTensorVacuumCoefficientClass
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.SupportedTensorVacuumCoefficientClass
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing module: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module: {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

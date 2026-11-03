import OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixNestedEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import Lean.Util.CollectAxioms
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open CyclotomicCrossingTensor
namespace NonVacuity.SwappedMatrixNestedEvaluation
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
private def m (_ : Bool) : ℕ := 10
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev bound := PowerWordContent.powerBound D cutoff L
private def Λ : Bool → ℤ := fun _ => 20

private abbrev Blocks := WeightBlocks D Λ (-Λ)
private abbrev Categories (a : Blocks) := ContentCategory D Sc cutoff bound a.1
private abbrev C := ELVWeightProduct D Sc cutoff bound Λ (-Λ)
private def R : Superfunctor ℚ C C := ⟨𝟭 _⟩
private def twoR : Mat_ (Superfunctor ℚ C C) := ⟨Bool, fun _ => R⟩
private def f : twoR ⟶ twoR := fun i j =>
  if i = j then 𝟙 R else if i = false then 𝟙 R else 0
private def g : twoR ⟶ twoR := fun i j =>
  if i = j then 𝟙 R else if i = false then -(𝟙 R) else 0
private theorem f_mem (i j : Bool) : f i j ∈ parity (R := ℚ) _ _ 0 := by
  unfold f
  split_ifs <;> first | exact id_mem R | exact Submodule.zero_mem _
private theorem g_mem (i j : Bool) : g i j ∈ parity (R := ℚ) _ _ 0 := by
  unfold g
  split_ifs
  · exact id_mem R
  · exact Submodule.neg_mem _ (id_mem R)
  · exact Submodule.zero_mem _

private theorem component_f_apply (M : C) (a : Blocks) (N : Categories a) (i j : Bool) :
    MatrixNestedEvaluation.component Categories f M a N i j =
      if i = j then 𝟙 ((M a).obj N) else if i = false then 𝟙 ((M a).obj N) else 0 := by
  cases i <;> cases j <;>
    simp [MatrixNestedEvaluation.component, MatrixEvaluation.map,
      MatrixProductEvaluation.evaluation, f, twoR, R, SuperNatTrans.total] <;> rfl
private theorem component_g_apply (M : C) (a : Blocks) (N : Categories a) (i j : Bool) :
    MatrixNestedEvaluation.component Categories g M a N i j =
      if i = j then 𝟙 ((M a).obj N) else if i = false then -(𝟙 ((M a).obj N)) else 0 := by
  cases i <;> cases j <;>
    simp [MatrixNestedEvaluation.component, MatrixEvaluation.map,
      MatrixProductEvaluation.evaluation, g, twoR, R, SuperNatTrans.total] <;> rfl

/-- The two-by-two inverse equations hold at every actual input module,
original-weight block and represented word. -/
private theorem component_fg (M : C) (a : Blocks) (N : Categories a) :
    MatrixNestedEvaluation.component Categories f M a N ≫
      MatrixNestedEvaluation.component Categories g M a N = 𝟙 _ := by
  apply Mat_.hom_ext
  intro i j
  change (∑ l : Bool, MatrixNestedEvaluation.component Categories f M a N i l ≫
    MatrixNestedEvaluation.component Categories g M a N l j) = _
  rw [Fintype.sum_bool]
  cases i <;> cases j <;> simp [component_f_apply, component_g_apply] <;> rfl
private theorem component_gf (M : C) (a : Blocks) (N : Categories a) :
    MatrixNestedEvaluation.component Categories g M a N ≫
      MatrixNestedEvaluation.component Categories f M a N = 𝟙 _ := by
  apply Mat_.hom_ext
  intro i j
  change (∑ l : Bool, MatrixNestedEvaluation.component Categories g M a N i l ≫
    MatrixNestedEvaluation.component Categories f M a N l j) = _
  rw [Fintype.sum_bool]
  cases i <;> cases j <;> simp [component_f_apply, component_g_apply] <;> rfl
private theorem component_f_isIso (M : C) (a : Blocks) (N : Categories a) :
    IsIso (MatrixNestedEvaluation.component Categories f M a N) :=
  ⟨MatrixNestedEvaluation.component Categories g M a N, component_fg M a N, component_gf M a N⟩
private theorem component_g_isIso (M : C) (a : Blocks) (N : Categories a) :
    IsIso (MatrixNestedEvaluation.component Categories g M a N) :=
  ⟨MatrixNestedEvaluation.component Categories f M a N, component_gf M a N, component_fg M a N⟩

/-- The nested criterion constructs the whole natural inverse in both
parity-profile orientations; no IsIso premise for f or g is supplied. -/
example : IsIso f := MatrixNestedEvaluation.isIso_of_components_target Categories f
  (fun _ => 0) f_mem component_f_isIso
example : IsIso g := MatrixNestedEvaluation.isIso_of_components_source Categories g
  (fun _ => 0) g_mem component_g_isIso

private abbrev ν : List Bool := []
private abbrev σ : List Bool := ν.reverse
private abbrev OldC := OldCategory D Sc cutoff
private abbrev wordTarget := powerWordModule D Sc cutoff L ν
private theorem powers_high (j : Bool × ℕ) : 16 ≤ L j * SKM.SYM.elementaryWeight D j := by
  change 16 ≤ 10 * (2 * (j.2 + 1))
  omega
private theorem bounded_injective :
    Function.Injective (fun x : ExtendedAtMost D originalSc σ σ 2 =>
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ x.val) :=
  powerWordHalfTurnCoordinate_injective_on_extendedAtMost D originalSc cutoff L
    (fun _ => (by decide : 16 ≤ 20)) powers_high (by decide)
private def identityNF : NFIdx σ σ := by
  change NFIdx ([] : List Bool) []
  have hc : Categorification.TypeA.canWord 0 (1 : Equiv.Perm (Fin 0)) = [] := by
    apply List.length_eq_zero_iff.mp
    rw [Categorification.TypeA.length_canWord, Categorification.TypeA.length_one]
  refine ⟨([], 1), by simp, by simp, ?_⟩
  simp only [List.map_nil, List.length_nil, hc, cw, List.reverse_nil,
    List.nil_append, QuiverHecke.pl, QuiverHecke.SChain]
private def oddIndex : SKM.SYM.CoefficientIndex D := (0, {⟨false, rfl⟩, ⟨true, rfl⟩})
private def occupied : ExtendedAtMost D originalSc σ σ 2 :=
  ⟨extensionBasis D originalSc σ σ (oddIndex, identityNF),
    Submodule.subset_span ⟨(oddIndex, identityNF), by decide, rfl⟩⟩
private theorem coordinate_ne_zero : (show wordTarget.obj (⟨ν⟩ : OldC) from
    powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val) ≠ 0 := by
  intro hz
  have hh : occupied = (0 : ExtendedAtMost D originalSc σ σ 2) := by
    apply bounded_injective
    change powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val =
      powerWordHalfTurnCoordinate D originalSc cutoff L σ σ 0
    exact hz.trans (map_zero _).symm
  exact (extensionBasis D originalSc σ σ).ne_zero (oddIndex, identityNF) (congrArg Subtype.val hh)

private def input : C := PowerWordWeight.wordFamily D Sc cutoff L Λ (-Λ) []
private def block : Blocks := ⟨0, blockWeight_zero D Λ⟩
private def wordObject : Categories block := ⟨⟨[]⟩, rfl⟩
private def vector : (input block).obj wordObject :=
  powerWordHalfTurnCoordinate D originalSc cutoff L σ σ occupied.val
example : vector ≠ 0 := coordinate_ne_zero

/-- The literal nested off-diagonal matrix entry fixes a surviving
product of the two odd coefficients at this actual ELV input. -/
private theorem offdiag_apply :
    (MatrixNestedEvaluation.component Categories f input block wordObject false true) vector = vector := by
  simp [component_f_apply]
  rfl

example : MatrixNestedEvaluation.component Categories f input block wordObject false true ≠ 0 := by
  intro hz
  have he := congrArg (fun h => h vector) hz
  rw [offdiag_apply] at he
  exact coordinate_ne_zero he

end NonVacuity.SwappedMatrixNestedEvaluation
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Supernatural.MatrixNestedEvaluation
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

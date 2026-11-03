import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedSectorChart
import OddMath.SKM.AugmentedInverseEvaluation
import Mathlib.Algebra.Category.ModuleCat.Ulift
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordHomCoordinates
import OddMath.QuiverHecke.HalfTurn.PowerWordCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.SwappedAssembly
open CyclotomicCrossingTensor
namespace NonVacuity.SwappedAugmentedSectorChart

local instance homPi (A B : PiSCat.{0, 0, 1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 20
private def L (_ : Bool × ℕ) : ℕ := 10
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private def highest : Bool → ℤ := fun _ => 20
private theorem cutoff_pairing : ∀ i, (cutoff i : ℤ) = D.h i highest := by
  intro i
  rfl
private def factor := elvRouquierFamily D Sc cutoff bound highest cutoff_pairing

/-- Both factors, their shifted left adjunctions and their multicolour
relations are constructed from the prescribed positive-level ELV family. -/
private def P : ProbeReservoir ℚ (PiSCat.{0, 0, 1} ℚ) D originalSc where
  T := factor
  W := factor
  leftAdj := factor.leftAdjoints
  probeRel := elvRouquierMulticolour D originalSc cutoff bound highest cutoff_pairing
  reservoirRel := elvRouquierMulticolour D originalSc cutoff bound highest cutoff_pairing
  ΛP := highest
  ΛR := highest


private def content : Bool →₀ ℕ := Finsupp.single false 1 + Finsupp.single true 1
private abbrev sector : Sector Bool := (content, content)
private theorem content_weight : contentWeight D content = D.α false + D.α true := by
  rw [content, map_add]
  simp [contentWeight, Finsupp.weight_apply]
private def identityHom : P.H sector := by
  change factor.obj (-(highest - contentWeight D content)) ⟶
    factor.obj (-highest + contentWeight D content)
  have h : -(highest - contentWeight D content) = -highest + contentWeight D content := by abel
  rw [h]
  exact 𝟙 _
private def coeff : P.CrossCoeff where
  a _ _ _ _ := 0
private theorem cup_valid (i : Bool) : StepValid (false, i) true sector := by
  cases i <;> simp [StepValid, content]


private def forgetSuperspace : SVec ℚ ⥤ ModuleCat ℚ where
  obj V := ModuleCat.of ℚ V
  map f := ModuleCat.ofHom f
  map_id _ := rfl
  map_comp _ _ := rfl
private instance : forgetSuperspace.Additive where
  map_add := by intros; rfl

/-- Evaluate an arbitrary full Hom at an actual module, output content,
and content-category object. No regular-input detection premise is used. -/
private def evaluation (t : Sector Bool) (N : P.T.obj (-P.muP t))
    (δ : WeightBlocks D highest (P.muM t))
    (a : ContentCategory D Sc cutoff bound δ.1) : P.H t ⥤ ModuleCat.{1} ℚ :=
  superfunctorTotalEvaluation (k := ℚ) N ⋙
    CategoryTheory.Pi.eval (fun β : WeightBlocks D highest (P.muM t) =>
      ContentModules D Sc cutoff bound β.1) δ ⋙
    superfunctorTotalEvaluation (k := ℚ) a ⋙ forgetSuperspace ⋙ ModuleCat.uliftFunctor.{1} ℚ
private instance evaluation_additive (t : Sector Bool) (N : P.T.obj (-P.muP t))
    (δ : WeightBlocks D highest (P.muM t))
    (a : ContentCategory D Sc cutoff bound δ.1) : (evaluation t N δ a).Additive := by
  let : (CategoryTheory.Pi.eval (fun β : WeightBlocks D highest (P.muM t) =>
      ContentModules D Sc cutoff bound β.1) δ).Additive := ⟨by intros; rfl⟩
  have h0 : (superfunctorTotalEvaluation (k := ℚ) (D := P.W.obj (P.muM t)) N).Additive := inferInstance
  have h2 : (superfunctorTotalEvaluation (k := ℚ) (D := SVec ℚ) a).Additive := inferInstance
  have h3 : forgetSuperspace.Additive := inferInstance
  have h4 : (ModuleCat.uliftFunctor.{1, 0} ℚ).Additive := inferInstance
  unfold evaluation
  infer_instance

example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosSectorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom (evaluation sector N δ a)
example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  P.augNegSectorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom (evaluation sector N δ a)
example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosSectorMatrix_eq_posMap (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom (evaluation sector N δ a)
example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  P.augNegSectorMatrix_eq_negMap (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom (evaluation sector N δ a)

private abbrev emptySector : Sector Bool := (0,0)
private def emptyHom : P.H emptySector := by
  change factor.obj (-highest) ⟶ factor.obj (-highest)
  exact 𝟙 _
example (i : Bool) : D.h i (P.wt emptySector) = 0 := by
  change D.h i ((highest - contentWeight D 0) + (-highest + contentWeight D 0)) = 0
  simp
example (i : Bool) (N : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D highest (P.muM emptySector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosSectorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt emptySector) emptySector emptyHom
    (evaluation emptySector N δ a)
example (i : Bool) (N : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D highest (P.muM emptySector))
    (a : ContentCategory D Sc cutoff bound δ.1) :=
  (P.augNegSourceIso (C := ModuleCat.{1} ℚ) i (P.wt emptySector) emptySector emptyHom
    (evaluation emptySector N δ a)).hom_inv_id

end NonVacuity.SwappedAugmentedSectorChart
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedSectorChart
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

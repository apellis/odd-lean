import OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedFactorMatrix
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
namespace NonVacuity.SwappedAugmentedFactorMatrix

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

/-- Mixed occupied content, both odd colours, and an actual identity Hom. -/
example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom
    (evaluation sector N δ v)
example (i : Bool) (N : P.T.obj (-P.muP sector))
    (δ : WeightBlocks D highest (P.muM sector))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augNegFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt sector) sector identityHom
    (evaluation sector N δ v)

private def ray (i : Bool) : Sector Bool := (0, Finsupp.single i 1)
private def coray (i : Bool) : Sector Bool := (Finsupp.single i 1, 0)
private theorem ray_weight (i : Bool) : P.wt (ray i) = D.α i := by
  change (highest - contentWeight D 0) + (-highest + contentWeight D (Finsupp.single i 1)) = _
  simp only [map_zero, sub_zero, contentWeight, Finsupp.weight_single, one_smul]
  abel
private theorem coray_weight (i : Bool) : P.wt (coray i) = -D.α i := by
  change (highest - contentWeight D (Finsupp.single i 1)) + (-highest + contentWeight D 0) = _
  simp only [map_zero, add_zero, contentWeight, Finsupp.weight_single, one_smul]
  abel
example (i : Bool) : D.h i (P.wt (ray i)) = 2 := by
  rw [ray_weight]
  cases i <;> decide
example (i : Bool) : D.h i (P.wt (coray i)) = -2 := by
  rw [coray_weight]
  cases i <;> decide

/-- These exact physical sectors have nonempty two-slot windows and
complementary absent corners. The Hom input is arbitrary. -/
example (i : Bool) (Z : P.H (ray i)) (N : P.T.obj (-P.muP (ray i)))
    (δ : WeightBlocks D highest (P.muM (ray i)))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt (ray i)) (ray i) Z
    (evaluation (ray i) N δ v)
example (i : Bool) (Z : P.H (coray i)) (N : P.T.obj (-P.muP (coray i)))
    (δ : WeightBlocks D highest (P.muM (coray i)))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augNegFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt (coray i)) (coray i) Z
    (evaluation (coray i) N δ v)
example (i : Bool) : ¬StepValid (dn i) true (ray i) := by cases i <;> simp [ray, StepValid]
example (i : Bool) : ¬StepValid (up i) false (coray i) := by cases i <;> simp [coray, StepValid]

private abbrev emptySector : Sector Bool := (0,0)
private def emptyHom : P.H emptySector := by
  change factor.obj (-highest) ⟶ factor.obj (-highest)
  exact 𝟙 _
example (i : Bool) : D.h i (P.wt emptySector) = 0 := by
  change D.h i ((highest - contentWeight D 0) + (-highest + contentWeight D 0)) = 0
  simp
example (i : Bool) (N : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D highest (P.muM emptySector))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augPosFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt emptySector) emptySector emptyHom
    (evaluation emptySector N δ v)
example (i : Bool) (N : P.T.obj (-P.muP emptySector))
    (δ : WeightBlocks D highest (P.muM emptySector))
    (v : ContentCategory D Sc cutoff bound δ.1) :=
  P.augNegFactorMatrix_square (C := ModuleCat.{1} ℚ) coeff i (P.wt emptySector) emptySector emptyHom
    (evaluation emptySector N δ v)

end NonVacuity.SwappedAugmentedFactorMatrix
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.AugmentedFactorMatrix
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owner {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations in {owner}"

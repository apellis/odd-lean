import OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendQuotientComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVOldAppendDot
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.QuiverHecke ELVOld
open ELVOld.BalancedInduction
open CyclotomicAction.AsymmetricParameters
namespace InductionSquareTransformConsumer
private def D : SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private abbrev cut (_ : Bool) : ℕ := 8
private abbrev Q := oldTruncateFunctor D Sc cut 8
private abbrev s : OldCategory D Sc cut := ⟨[false, true]⟩
private def M := induced Q (oldRepresentable D Sc cut s)
private abbrev J (i : Bool) := CyclotomicCrossingTensor.append D Sc cut i
private abbrev T (i : Bool) := truncatedAppend D Sc cut 8 [i]
private abbrev RM := weightedRestriction D Sc cut 8 M

/-- The canonical map changes the full old coefficient arrow to its quotient. -/
example (i : Bool) (w : OldCategory D Sc cut) (g : (J i).obj s ⟶ w)
    (b : M.obj (Q.obj s)) :
    coendSquareMap (J i) Q Q (T i) (oldAppend_truncate D Sc cut 8 i) M.toFunctor w
      (tensor (J i) RM.toFunctor s g b) =
    tensor (T i) M.toFunctor (Q.obj s) (Q.map g) b := by
  change coendSquareMap (J i) Q Q (T i) (oldAppend_truncate D Sc cut 8 i) M.toFunctor w
    (tensor (J i) (Q ⋙ M.toFunctor) s g b) = _
  have hx := coendSquareMap_tensor (J i) Q Q (T i)
    (oldAppend_truncate D Sc cut 8 i) M.toFunctor w s g b
  simpa only [eqToHom_refl, Category.id_comp] using hx

/-- Both moving parities, with every old output arrow and every module vector. -/
example (i : Bool) (w : OldCategory D Sc cut) :
    coendSquareMap (J i) Q Q (T i) (oldAppend_truncate D Sc cut 8 i) M.toFunctor w ∘ₗ
      transformLinear (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut i) RM w =
    transformLinear (truncatedAppendComponent_supernatural D Sc cut 8 (by
      simpa only [pow_one, one_nsmul] using firstDot_pow_parity D Sc i [] 1)) M (Q.obj w) ∘ₗ
      coendSquareMap (J i) Q Q (T i) (oldAppend_truncate D Sc cut 8 i) M.toFunctor w := by
  apply coendSquareMap_transform
  intro v
  change 𝟙 _ ≫ Q.map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut i v) =
    truncatedAppendComponent D Sc cut 8 (dotE D Sc [i] 0) (Q.obj v) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]
  rfl

/-- The odd coefficient arrow has its negative twist before quotienting. -/
example : Q.map (twist ℚ 1
    (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s)) =
    -Q.map (CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s) := by
  have hp := (CyclotomicCrossingTensor.oldAppendDot_supernatural D Sc cut true).mem s
  change CyclotomicCrossingTensor.oldAppendDotComponent D Sc cut true s ∈
    parity (R := ℚ) _ _ 1 at hp
  rw [twist_of_mem 1 hp]
  simp

end InductionSquareTransformConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVInductionSquareTransform
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owner"
  for name in names do
    for ax in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations"

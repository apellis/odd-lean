import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingQuotient
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor.Distinct
namespace DistinctCrossingQuotientExamples

private def D : SKM.Datum Bool (Bool → ℤ) :=
  { AsymmetricParameters.datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => AsymmetricParameters.datum.even_of_odd i j rfl }
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num
private def cutoff (n : ℕ) (_ : Bool) := n
private theorem distinct (i : Bool) : i ≠ !i := by cases i <;> decide

/-- Both mixed moving parities, with arbitrary cutoff and matching corners. -/
example (n : ℕ) (i : Bool) :=
  cyclotomicEquiv D Sc (cutoff n) i (!i) (distinct i) [!i, i] [i, i]

/-- The distinct vacuum boundary and zero cutoff are included literally. -/
example (i : Bool) := cyclotomicEquiv D Sc (cutoff 0) i (!i) (distinct i) [] []

private def oddCoefficient (n : ℕ) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D (cutoff n) :=
  SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩)
private def exteriorArrow (n : ℕ) (i : Bool) : hom D Sc (cutoff n) [i] [i] :=
  oddCoefficient n ⊗ₜ[ℚ] 𝟙 ((pres D Sc).obj (ob D [i]))
private def identityArrow (n : ℕ) (i : Bool) : hom D Sc (cutoff n) [i] [i] :=
  affineUnit D Sc (cutoff n) _ _ (𝟙 _)

/-- The actual map on a full exterior-coefficient balanced tensor. -/
example (n : ℕ) (i : Bool) := toCyclotomic_tensor_mk D Sc (cutoff n)
  i (!i) [!i] [] [i] (exteriorArrow n i) (identityArrow n (!i))

/-- Explicit PBW inversion of the exterior-coefficient mixed crossing. -/
example (n : ℕ) (i : Bool) := cyclotomicEquiv_symm_mk D Sc (cutoff n)
  i (!i) (distinct i) [!i] [i]
  (rightContext D Sc (cutoff n) [i] _ _ (identityArrow n (!i)) ≫
    affineUnit D Sc (cutoff n) _ _ (crossLast D Sc [] (!i) i) ≫
    rightContext D Sc (cutoff n) [!i] _ _ (exteriorArrow n i))

/-- Two distinct odd colours retain the nontrivial crossing parity. -/
example (n : ℕ) := cyclotomicEquiv AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true (by decide) [true] [false]
example (n : ℕ) := decode_comp_shortCross AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true (by decide) [true] [false]

end DistinctCrossingQuotientExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingTensor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctAppendTails,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingPowers,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingKernel,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingQuotient] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"

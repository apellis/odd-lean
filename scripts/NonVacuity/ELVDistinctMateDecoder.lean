import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctMateDecoder
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor CyclotomicCrossingTensor.Distinct
namespace DistinctMateDecoderExamples

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

/-- The prescribed categorical mate is inverted on matching old representable corners. -/
example (n : ℕ) (i : Bool) :=
  moduleMateEquiv D Sc (cutoff n) i (!i) (distinct i) [!i, i] [i, i]

/-- Empty corners and zero cutoff retain their literal source and target. -/
example (i : Bool) := moduleMateEquiv D Sc (cutoff 0) i (!i) (distinct i) [] []

private def oddCoefficient (n : ℕ) : SKM.SYM.ELVCoefficientAlgebra (k := ℚ) D (cutoff n) :=
  SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩)
private def exteriorArrow (n : ℕ) (i : Bool) : hom D Sc (cutoff n) [i] [i] :=
  oddCoefficient n ⊗ₜ[ℚ] 𝟙 ((pres D Sc).obj (ob D [i]))
private def identityArrow (n : ℕ) (i : Bool) : hom D Sc (cutoff n) [i] [i] :=
  affineUnit D Sc (cutoff n) _ _ (𝟙 _)

private def exteriorTensor (n : ℕ) (i : Bool) : ModuleSource D Sc (cutoff n) i (!i) [!i] [i] :=
  BalancedInduction.tensor (append D Sc (cutoff n) i)
    ((BalancedInduction.restriction (append D Sc (cutoff n) (!i))).obj
      (oldRepresentable D Sc (cutoff n) (⟨[!i]⟩ : OldCategory D Sc (cutoff n)))).toFunctor
    (⟨[]⟩ : OldCategory D Sc (cutoff n))
    ((ideal D Sc (cutoff n) [i] [i]).mkQ (exteriorArrow n i))
    ((ideal D Sc (cutoff n) [!i] [!i]).mkQ (identityArrow n (!i)))

/-- Equality to the literal rectangular cup-crossing-cap on a tensor carrying
an odd coefficient in its first factor. -/
example (n : ℕ) (i : Bool) := moduleMateEquiv_apply D Sc (cutoff n)
  i (!i) (distinct i) [!i] [i] (exteriorTensor n i)

/-- Both directions of canonical J retain the full exterior coefficient. -/
example (n : ℕ) (i : Bool) := moduleSourceParityEquiv_tensor D Sc (cutoff n)
  i (!i) [!i] [] [i]
  ((ideal D Sc (cutoff n) [i] [i]).mkQ (exteriorArrow n i))
  ((ideal D Sc (cutoff n) [!i] [!i]).mkQ (identityArrow n (!i)))

/-- Distinct odd colours test the positive crossing with its nonzero shift. -/
example (n : ℕ) := moduleMateEquiv AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true (by decide) [true] [false]
example (n : ℕ) := sourceParityEquiv AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true [true] [false]

private def allOddArrow (n : ℕ) :
    hom AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) [false] [false] :=
  SKM.SYM.elvCoefficientQuotient AsymmetricParameters.datum (cutoff n)
    (SKM.SYM.delta AsymmetricParameters.datum ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres AsymmetricParameters.datum AsymmetricParameters.scalars).obj
        (ob AsymmetricParameters.datum [false]))

/-- The odd source shift acts on a first tensor factor with an exterior coefficient. -/
example (n : ℕ) := moduleSourceParityEquiv_tensor
  AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n)
  false true [true] [] [false]
  ((ideal AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) [false] [false]).mkQ
    (allOddArrow n))
  ((ideal AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) [true] [true]).mkQ
    (affineUnit AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n) _ _ (𝟙 _)))

end DistinctMateDecoderExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedCrossTensor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVInductionMixedMateTensor,
      `OddMath.QuiverHecke.CyclotomicAction.ELVSCatRectangularMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctSourceParity,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctMateDecoder] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"

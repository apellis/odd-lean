import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleIso
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.CyclotomicAction
open CyclotomicCrossingTensor CyclotomicCrossingTensor.Distinct
namespace DistinctModuleIsoExamples

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

private def shiftedModule (n : ℕ) (v : List Bool) :=
  supermoduleParityObj (oldRepresentable D Sc (cutoff n) (⟨v⟩ : OldCategory D Sc (cutoff n)))

/-- Both mixed moving parities have the prescribed module-level forward map. -/
example (n : ℕ) (i : Bool) := moduleMateIso D Sc (cutoff n)
  i (!i) (distinct i) (shiftedModule n [!i])
example (n : ℕ) (i : Bool) := moduleMateIso_hom D Sc (cutoff n)
  i (!i) (distinct i) (shiftedModule n [!i])
example (n : ℕ) (i : Bool) := moduleMateIso_inv_mem D Sc (cutoff n)
  i (!i) (distinct i) (shiftedModule n [!i])

/-- Empty words and zero cutoff keep their actual coend domains. -/
example (i : Bool) := moduleMateIso D Sc (cutoff 0)
  i (!i) (distinct i) (shiftedModule 0 [])

private def exteriorEnd (n : ℕ) (j : Bool) :
    (⟨[j]⟩ : OldCategory D Sc (cutoff n)) ⟶ ⟨[j]⟩ :=
  (ideal D Sc (cutoff n) [j] [j]).mkQ
    (SKM.SYM.elvCoefficientQuotient D (cutoff n) (SKM.SYM.delta D ℚ ⟨true, rfl⟩) ⊗ₜ[ℚ]
      𝟙 ((pres D Sc).obj (ob D [j])))

/-- Literal ordinary right covariance retains an odd exterior precomposition. -/
example (n : ℕ) (i : Bool) := kernelMateComponent_precompose D Sc (cutoff n)
  i (!i) (⟨[!i]⟩ : OldCategory D Sc (cutoff n)) ⟨[!i]⟩ ⟨[i]⟩ (exteriorEnd n (!i))

/-- Distinct odd colours test the nontrivial crossing parity on a shifted module. -/
example (n : ℕ) := moduleMateIso AsymmetricParameters.datum AsymmetricParameters.scalars
  (cutoff n) false true (by decide)
  (supermoduleParityObj (oldRepresentable AsymmetricParameters.datum AsymmetricParameters.scalars
    (cutoff n) (⟨[true]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n))))

/-- The entire chosen mate is inverted, with arbitrary input-module naturality. -/
example (n : ℕ) (i : Bool) := moduleMateFunctorIso D Sc (cutoff n) i (!i) (distinct i)
example (n : ℕ) (i : Bool) := moduleMateFunctorIso_hom D Sc (cutoff n) i (!i) (distinct i)
example (n : ℕ) := moduleMateFunctorIso_inv_mem AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) false true (by decide)
example (n : ℕ) := (moduleMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) false true (by decide)).hom_inv_id
example (n : ℕ) := (moduleMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) false true (by decide)).inv_hom_id

/-- Odd input-module maps retain the signed supernatural inverse law. -/
example (n : ℕ) := (moduleMateFunctorIso AsymmetricParameters.datum
  AsymmetricParameters.scalars (cutoff n) false true (by decide)).inv.naturality 1
    (supermoduleParityIso (oldRepresentable AsymmetricParameters.datum
      AsymmetricParameters.scalars (cutoff n)
      (⟨[]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n)))).hom
    (supermoduleParityIso_hom_mem (oldRepresentable AsymmetricParameters.datum
      AsymmetricParameters.scalars (cutoff n)
      (⟨[]⟩ : OldCategory AsymmetricParameters.datum AsymmetricParameters.scalars (cutoff n))))

end DistinctModuleIsoExamples

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.Algebra.HomogeneousSuperfunctorIso,
      `OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleIso] do
    let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module {owner}"
    let names := env.header.moduleData[idx]!.constNames
    if names.isEmpty then throwError "Empty owned module {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited all {names.size} declarations in {owner}"

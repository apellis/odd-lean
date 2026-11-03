import OddMath.QuiverHecke.SwappedAssembly.ReservoirVacuumDot
import OddMath.QuiverHecke.CyclotomicAction.ELVRouquierMulticolour
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedPowerCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import OddMath.SKM.RouquierFTriangle
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open OddMath.QuiverHecke.SwappedAssembly
open BalancedInduction PowerVacuumCoefficient
namespace NonVacuity.SwappedReservoirVacuumDot

local instance homPi (A B : PiSCat.{0, 0, 1} ℚ) : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private abbrev D := CyclotomicAction.AsymmetricParameters.datum
private abbrev originalSc := CyclotomicAction.AsymmetricParameters.scalars
private abbrev Sc := parameterTwist D originalSc
private def cutoff (_ : Bool) : ℕ := 4
private def L (_ : Bool × ℕ) : ℕ := 4
private abbrev bound := SKM.SYM.elvPowerWeightBound D cutoff L + 1
private def highest : Bool → ℤ := fun _ => 4
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

/-- The whole lowest-weight regular-power family, retaining every formal
content block. -/
private def regularInput : ELVWeightProduct D Sc cutoff bound highest (-highest) :=
  fun β => (restriction (contentInclusion D Sc cutoff bound β.1)).obj
    (weightedVacuum D Sc cutoff L)
private def zeroBlock : WeightBlocks D highest (-highest) := ⟨0, by simp [blockWeight]⟩
private abbrev star : ContentCategory D Sc cutoff bound 0 := ⟨⟨[]⟩, rfl⟩
private abbrev AQ := CoefficientPowerQuotient (k := ℚ) D cutoff L
private def deltaClass : AQ :=
  coefficientPowerQuotientMap (k := ℚ) D cutoff L (SKM.SYM.delta D ℚ ⟨false, rfl⟩)
private theorem powers_high (a : Bool × ℕ) :
    4 ≤ L a * SKM.SYM.elementaryWeight D a := by
  change 4 ≤ 4 * SKM.SYM.elementaryWeight D a
  have hw : 0 < SKM.SYM.elementaryWeight D a := by
    unfold SKM.SYM.elementaryWeight
    split_ifs <;> omega
  omega
private theorem delta_ne_zero : deltaClass ≠ 0 := by
  intro hz
  have hi := coefficientPowerQuotient_injective (k := ℚ) D cutoff L 1 4 (by decide)
    (fun _ => by rfl) powers_high
  have he := hi (a₁ := ⟨_, SKM.SYM.delta_mem_coefficientAtMost D ℚ ⟨false, rfl⟩⟩)
    (a₂ := 0) (by simpa only [deltaClass, ZeroMemClass.coe_zero, map_zero] using hz)
  have hδ : SKM.SYM.delta D ℚ ⟨false, rfl⟩ ≠ 0 := by
    rw [← SKM.SYM.coefficientBasis_delta]
    exact (SKM.SYM.coefficientBasis D ℚ).ne_zero _
  exact hδ (congrArg Subtype.val he)
private def occupied : (regularInput zeroBlock).obj star :=
  weightedEmptyEquiv D Sc cutoff L deltaClass
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro hz
  exact delta_ne_zero ((weightedEmptyEquiv D Sc cutoff L).injective
    (hz.trans (map_zero _).symm))

private theorem strand_valid (i : Bool) :
    StepValid (true, i) false (0, Finsupp.single i 1) := by
  simp [StepValid]
private def identityHom (i : Bool) :
    P.H (nextSector (true, i) false (0, Finsupp.single i 1)) := by
  change factor.obj (-(highest - contentWeight D 0)) ⟶
    factor.obj (-highest + contentWeight D (Finsupp.single i 1 - Finsupp.single i 1))
  simp only [tsub_self, map_zero, sub_zero, add_zero]
  exact 𝟙 _

/-- The actual occupied reservoir entry at each of two odd colours has
the factor's original dot in its zero-shift chart. -/
example (i : Bool) := P.dotImage_reservoirVacuum i 0 (Finsupp.single i 1)
  (strand_valid i) (strand_valid i) (identityHom i)

/-- The identity Hom in this consumer has a nonzero odd coefficient
input in the literal lowest-weight regular-power family. -/
example : occupied ≠ 0 := occupied_ne_zero

end NonVacuity.SwappedReservoirVacuumDot

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.ReservoirVacuumDot
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

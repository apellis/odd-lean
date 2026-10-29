import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveExtraction
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveSquareProduct
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned := #[`OddMath.QuiverHecke.CyclotomicAction.LeadingMoveTransport,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveProduct,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveOrderedCoefficients,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveExtraction,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveSquareProduct]
  let mut modules : Nat := 0
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if owned.contains env.header.moduleNames[i]! then
      modules := modules + 1
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  unless modules == owned.size do throwError "Missing owned module"
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations across {modules} modules"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification Categorification.TypeA
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
open scoped Classical
namespace LeadingMoveOrderedProductConsumer
local instance : DecidableEq Bool := fun a b => Classical.propDecidable (a = b)
open OddMath

def mixedDatum : OddMath.SKM.Datum Bool (Bool → ℤ) :=
  { datum with
    parity := fun i => if i then 1 else 0
    even_of_odd := fun i j _ => datum.even_of_odd i j rfl }

def mixedScalars : OddMath.SKM.Scalars mixedDatum ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := by intro _; norm_num

example (i : Bool) (l ν : List Bool) (c : MoveChoices ν) :
    collectedSourceSign mixedDatum (k := ℚ) (l ++ i :: ν)
      (leadingMoveBlocks mixedDatum i l ν c) = 1 :=
  collectedSourceSign_leadingMoveBlocks mixedDatum i l ν c

example (i : Bool) (l ν : List Bool) :
    leadingMoveEndpointPolynomial mixedDatum mixedScalars i l ν =
      OddMath.SKM.zsign ℚ (mixedDatum.parity i) ^ ν.count i •
        leadingMoveSquareProduct mixedDatum mixedScalars i l ν := by
  simpa using leadingMoveEndpointPolynomial_eq_sign_smul_squareProduct mixedDatum mixedScalars i l ν

example (i : Bool) (ν : List Bool) (m : ℕ) :
    prependWordCoefficients mixedDatum mixedScalars i ⟨ν, rfl⟩ (appendWord i ⟨ν, rfl⟩)
      (moveHom mixedDatum mixedScalars i [] ν) (longPrependShuffle ν.length, m) =
      leadingMoveOrderedCoefficients mixedDatum mixedScalars i ν
        (longPrependShuffle ν.length, m) :=
  prependWordCoefficients_moveHom_ordered mixedDatum mixedScalars i ν m

example (i : Bool) (n : ℕ) (β : Multiset Bool) (m : ℕ) :
    prependCoefficients mixedDatum mixedScalars i n (contentMove mixedDatum mixedScalars i n β)
      (longPrependShuffle n, m) = leadingMoveContentCoefficient mixedDatum mixedScalars i n β m :=
  contentMove_long_prependCoefficients_explicit mixedDatum mixedScalars i n β m

example (a : Bool → Polynomial ℚ) (n : ℕ) (β : Multiset Bool) (i : Bool)
    (b : CyclotomicContentCorner mixedDatum mixedScalars a n β) (m : ℕ) :
    appendContentRhoExtract mixedDatum mixedScalars a n β i
      (appendContentMoveLift mixedDatum mixedScalars a n β i b) m =
      (∑ s ∈ Finset.univ.filter (fun s : Word Bool (n + 1) => wordContent s = β),
        ∑ c : MoveChoices s.1,
          if sourceMovingDegree (leadingSourceDots mixedDatum i 0 0 s.1 c) = m then
            leadingMoveCoeff mixedDatum (k := ℚ) i s.1 c •
              FiniteHomMatrix.single s s (wordEndpointDots mixedDatum mixedScalars s
                (sourceOldDots (leadingSourceDots mixedDatum i 0 0 s.1 c)))
          else 0) • b :=
  appendContentMoveLift_extract_sum mixedDatum mixedScalars a n β i b m

end LeadingMoveOrderedProductConsumer

import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveCoefficients
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let owned := #[`OddMath.QuiverHecke.CyclotomicAction.LeadingIntertwinerExpansion,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveExpansion,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMovePolynomial,
    `OddMath.QuiverHecke.CyclotomicAction.LeadingMoveCoefficients]
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
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification.TypeA
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace LeadingMovePolynomialConsumer

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

/-- The actual leading chain, at arbitrary word length and either moving parity. -/
example (i : Bool) (l ν : List Bool) :
    leadingMoveHom mixedDatum mixedScalars i l ν -
      leadingMoveEndpointPolynomial mixedDatum mixedScalars i l ν ≫
        cl mixedDatum mixedScalars _ _ (cw (leadingMoveWord l ν))
          (leadingMoveWord_sChain i l ν) ∈
      Low mixedDatum mixedScalars (l ++ i :: ν) (l ++ ν ++ [i]) ν.length :=
  leadingMoveHom_sub_endpointPolynomial_mem_low mixedDatum mixedScalars i l ν

example (i : Bool) (l ν : List Bool) :
    moveHom mixedDatum mixedScalars i l ν -
      leadingMoveEndpointPolynomial mixedDatum mixedScalars i l ν ≫
        cl mixedDatum mixedScalars _ _ (cw (leadingMoveWord l ν))
          (leadingMoveWord_sChain i l ν) ∈
      Low mixedDatum mixedScalars (l ++ i :: ν) (l ++ ν ++ [i]) ν.length :=
  moveHom_sub_endpointPolynomial_mem_low mixedDatum mixedScalars i l ν

example (i : Bool) (n : ℕ) (β : Multiset Bool) (m : ℕ) :
    prependCoefficients mixedDatum mixedScalars i n (contentMove mixedDatum mixedScalars i n β)
      (longPrependShuffle n, m) =
    prependCoefficients mixedDatum mixedScalars i n
      (collectedContentMove mixedDatum mixedScalars i n β) (longPrependShuffle n, m) :=
  contentMove_long_prependCoefficients mixedDatum mixedScalars i n β m

example (a : Bool → Polynomial ℚ) (n : ℕ) (β : Multiset Bool) (i : Bool)
    (b : CyclotomicContentCorner mixedDatum mixedScalars a n β) (m : ℕ) :
    appendContentRhoExtract mixedDatum mixedScalars a n β i
      (appendContentMoveLift mixedDatum mixedScalars a n β i b) m =
      (OddMath.SKM.zsign ℤ (mixedDatum.parity i * Multiset.sum (Multiset.map mixedDatum.parity β))) ^ m •
        (homMatrixTwist mixedDatum mixedScalars (n + 1) (appendContentParity mixedDatum a β i)
          (prependCoefficients mixedDatum mixedScalars i (n + 1)
            (collectedContentMove mixedDatum mixedScalars i (n + 1) β)
            (longPrependShuffle (n + 1), m)) • b) :=
  appendContentMoveLift_extract_collected mixedDatum mixedScalars a n β i b m

#print axioms OddMath.QuiverHecke.leadingMoveHom_sub_endpointPolynomial_mem_low
#print axioms OddMath.QuiverHecke.contentMove_long_prependCoefficients_sum
#print axioms OddMath.QuiverHecke.appendContentMoveLift_extract_collected
end LeadingMovePolynomialConsumer

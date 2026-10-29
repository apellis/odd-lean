import OddMath.QuiverHecke.CyclotomicAction.AppendContentMoveCoordinates
import OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
import Lean.Util.CollectAxioms

open Lean Elab Command
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.QuiverHecke.CyclotomicAction.AppendContentMoveCoordinates then
      for n in env.header.moduleData[i]!.constNames do
        for a in (← Lean.collectAxioms n) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains a do
            throwError "Disallowed {a} in {n}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} declarations"

noncomputable section
open CategoryTheory StringDiagrams OddMath.QuiverHecke Categorification
open OddMath.QuiverHecke.CyclotomicAction.AsymmetricParameters
namespace AppendContentMoveCoordinatesConsumer

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

example : mixedDatum.parity false = 0 := rfl
example : mixedDatum.parity true = 1 := rfl

/-- All-height coordinate extraction in a datum containing both parities. -/
theorem coordinate (a : Bool → Polynomial ℚ) (n : ℕ) (β : Multiset Bool)
    (i : Bool) (b : CyclotomicContentCorner mixedDatum mixedScalars a n β) (m : ℕ) :
    appendContentRhoExtract mixedDatum mixedScalars a n β i
        (appendContentMoveLift mixedDatum mixedScalars a n β i b) m =
      (OddMath.SKM.zsign ℤ
        (mixedDatum.parity i * Multiset.sum (Multiset.map mixedDatum.parity β))) ^ m •
        (homMatrixTwist mixedDatum mixedScalars (n + 1)
          (appendContentParity mixedDatum a β i)
          (prependCoefficients mixedDatum mixedScalars i (n + 1)
            (contentMove mixedDatum mixedScalars i (n + 1) β)
            (longPrependShuffle (n + 1), m)) • b) :=
  appendContentMoveLift_extract mixedDatum mixedScalars a n β i b m

example (a : Bool → Polynomial ℚ) (n m : ℕ) (β : Multiset Bool)
    (b : CyclotomicContentCorner mixedDatum mixedScalars a n β) :=
  coordinate a n β false b m

example (a : Bool → Polynomial ℚ) (n m : ℕ) (β : Multiset Bool)
    (b : CyclotomicContentCorner mixedDatum mixedScalars a n β) :=
  coordinate a n β true b m

example (i : Bool) (s t : List Bool)
    (h : (pres mixedDatum mixedScalars).obj (ob mixedDatum (i :: s)) ⟶
      (pres mixedDatum mixedScalars).obj (ob mixedDatum t))
    (hh : h ∈ Low mixedDatum mixedScalars (i :: s) t s.length)
    (x : PrependIdx i s t) (hx : x.1.2.2.2 = longPrependShuffle s.length) :
    (prependBasis mixedDatum mixedScalars).repr h x = 0 :=
  prependBasis_long_repr_eq_zero_of_low mixedDatum mixedScalars i s t h hh x hx

example (r : ℕ) :
    cw (Categorification.TypeA.canWord (r + 1) (longPrependShuffle r).1⁻¹) =
      (List.range r).map PG.cross := cw_longPrependShuffle r

#print axioms OddMath.QuiverHecke.appendContentMoveLift_extract
#print axioms OddMath.QuiverHecke.prependBasis_long_repr_eq_zero_of_low
end AppendContentMoveCoordinatesConsumer

import OddMath.QuiverHecke.CyclotomicAction.ELVOutputLongExtraction
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Categorification.TypeA
open OddMath OddMath.QuiverHecke OddMath.QuiverHecke.ELVOld
open scoped TensorProduct Classical
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

-- All colours and words; the sign is evaluated, not an existential unit.
example (i : I) (v : List I) :
    sourceDotSign D (k := k) (i :: v)
      (canWord (v.length + 1) (longPrependShuffle v.length).1⁻¹) v.length =
    SKM.zsign k (D.parity i * wordSumParity D v) :=
  sourceDotSign_longPrependShuffle_last D i v

-- The producer acts on the old-only quotient, with no assumed coordinate maps.
example (p : ZMod 2) (i : I) (v : List I) (m : ℕ) (c : k)
    (z z' : Target D Sc cutoff i v (v ++ [i])) :
    outputLongCoordinate D Sc cutoff p i v m (z + c • z') =
      outputLongCoordinate D Sc cutoff p i v m z +
        c • outputLongCoordinate D Sc cutoff p i v m z' := by
  rw [map_add, map_smul]

-- Arbitrary exterior coefficient and arbitrary balance parity survive descent.
example (p : ZMod 2) (i : I) (s t : List I)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) (m : ℕ)
    (h : SChain (i :: s)
      (pl (i :: s) (cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹) ++
        (List.replicate m s.length).map PG.dot)) t) :
    ∃ h' : SChain (i :: s)
      (pl (i :: s) ((List.replicate m 0).map PG.dot ++
        cw (canWord (s.length + 1) (longPrependShuffle s.length).1⁻¹))) t,
      ∀ (x : PrependIdx i s t), x.1.2.2.2 = longPrependShuffle s.length →
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h)) =
      (SKM.zsign k (D.parity i * wordSumParity D s)) ^ m •
      prependOldCoordinate D Sc cutoff p x
        (projection D Sc cutoff i s t (a ⊗ₜ[k] cl D Sc _ _ _ h')) :=
  prependOldCoordinate_long_last_dots D Sc cutoff p i s t a m h

example (p : ZMod 2) (i : I) (m : ℕ) :
    outputLongCoordinate D Sc (fun _ => 0) p i [] m 0 = 0 := map_zero _

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for owner in #[`OddMath.QuiverHecke.CyclotomicAction.LongOutputDotTransport,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputDotCoordinates,
      `OddMath.QuiverHecke.CyclotomicAction.ELVOutputLongExtraction] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Missing module {owner}"
    let mut count : Nat := 0
    for name in env.header.moduleData[idx]!.constNames do
      let axioms ← Lean.collectAxioms name
      for axiomName in axioms do
        unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
          throwError "Disallowed axiom {axiomName} in {name}"
      logInfo m!"AUDIT {owner} {name}: {axioms}"
      count := count + 1
    if count == 0 then throwError "Empty declaration inventory for {owner}"
    logInfo m!"Audited {count} declarations in {owner}; all axioms allowed."

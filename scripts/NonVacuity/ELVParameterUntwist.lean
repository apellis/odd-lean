import OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist
import Lean.Util.CollectAxioms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVParameterUntwist
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owned module"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations audited"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

/-!
Symbolic consumers of the mixed quadratic parameter evaluation. The target
algebra and its left module are arbitrary, not numerical specializations.
-/
noncomputable section
open OddMath OddMath.QuiverHecke

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X]
  (D : SKM.Datum I X) [CommRing k] (Sc : SKM.Scalars D k)
  {R M : Type*} [Ring R] [Algebra k R] [AddCommGroup M] [Module R M]

example (i j : I) (p q : ℕ) (h : ZMod 2) (hs : Sc.s i j p q ≠ 0) :
    elvOrderedDotExponent D i j p q h =
      D.parity i * (p / 2 : ℕ) + D.parity j * (q / 2 : ℕ) := by
  obtain ⟨hp, hq⟩ := elvParameter_support D Sc hs
  exact elvOrderedDotExponent_of_support D i j p q h hp hq

example (i j : I) (p q : ℕ) (h : ZMod 2) (z A B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        ((parameterTwist D Sc).s j i q p • (z * (A ^ q * B ^ p))) =
      Sc.s i j p q • (SKM.zsign k (elvOrderedDotExponent D i j p q h) •
        (z * (A ^ q * B ^ p))) :=
  parameterTwist_s_reversed_eval D Sc i j p q h z A B

example {i j : I} (hij : i ≠ j) (h : ZMod 2) (z B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        (((parameterTwist D Sc).t i j : k) • (z * B ^ D.dn i j)) =
      (Sc.t i j : k) •
        (SKM.zsign k (elvOrderedDotExponent D i j (D.dn i j) 0 h) •
          (z * B ^ D.dn i j)) :=
  parameterTwist_t_eval D Sc hij h z B

example {i j : I} (hij : i ≠ j) (A B : R) :
    SKM.zsign k (D.parity i * D.parity j) •
        pairQuadPoly D (parameterTwist D Sc) j i A B =
      elvSignedPairQuadEval D Sc j i A B :=
  pairQuadPoly_parameterTwist_reversed_eval D Sc hij A B

example {i j : I} (hij : i ≠ j) (z A B : R) (m : M) :
    (z * (SKM.zsign k (D.parity i * D.parity j) •
      pairQuadPoly D (parameterTwist D Sc) j i A B)) • m =
      (z * elvSignedPairQuadEval D Sc j i A B) • m :=
  pairQuadPoly_parameterTwist_module D Sc hij z A B m

example [Fintype I] {i j : I} (hij : i ≠ j) (n : ℕ)
    (f : Hn D (parameterTwist D Sc) (n + 1 + 1) →ₐ[k] R) :
    SKM.zsign k (D.parity i * D.parity j) •
      (f (affineLastCrossing D (parameterTwist D Sc) i j n) *
        f (affineLastCrossing D (parameterTwist D Sc) j i n)) =
      f (appendAlgebra D (parameterTwist D Sc) i (n + 1)
        (appendAlgebra D (parameterTwist D Sc) j n 1)) *
      elvSignedPairQuadEval D Sc j i
        (f (appendAlgebra D (parameterTwist D Sc) i (n + 1)
          (affineLastDot D (parameterTwist D Sc) j n)))
        (f (affineLastDot D (parameterTwist D Sc) i (n + 1))) :=
  affineLastCrossing_parameterUntwist_eval D Sc hij n f

#print axioms OddMath.QuiverHecke.affineLastCrossing_parameterUntwist_eval
#print axioms OddMath.QuiverHecke.elvOrderedDotExponent_of_support
#print axioms OddMath.QuiverHecke.elvParameter_support
#print axioms OddMath.QuiverHecke.parameterSignExponent_untwist
#print axioms OddMath.QuiverHecke.parameterTwist_s_reversed_eval
#print axioms OddMath.QuiverHecke.parameterTwist_t_eval
#print axioms OddMath.QuiverHecke.pairQuadPoly_parameterTwist_eval
#print axioms OddMath.QuiverHecke.pairQuadPoly_parameterTwist_reversed_eval
#print axioms OddMath.QuiverHecke.pairQuadPoly_parameterTwist_module

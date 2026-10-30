import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPolynomial
import Lean.Util.CollectAxioms

/-! Arbitrary-ring consumers and a noncommutative rational matrix instance.
All degrees are unrestricted, including zero. -/
open Finset
open OddMath.QuiverHecke.SwappedAssembly.RepeatedOuterPolynomial

section Generic
variable {k R : Type*} [CommRing k] [Ring R] [Algebra k R]

example (A x z : R) (h : x * z = -(z * x))
    (hA : A * (x * x - z * z) = x - z) (n : ℕ) :
    A * (x ^ (2 * n) - z ^ (2 * n)) =
      ∑ a ∈ range (2 * n), (-1 : k) ^ a • (x ^ (2 * n - 1 - a) * z ^ a) :=
  odd_correction_smul A x z h hA n

example {ι : Type*} (s : Finset ι) (w : ι → k) (n c : ι → ℕ)
    (A x z m : R) (h : x * z = -(z * x))
    (hA : A * (x * x - z * z) = x - z) (hm : Commute z m) :
    A * (∑ t ∈ s, w t • ((x ^ (2 * n t) - z ^ (2 * n t)) * m ^ (c t))) =
      ∑ t ∈ s, w t • (∑ a ∈ range (2 * n t),
        (-1 : k) ^ a • (x ^ (2 * n t - 1 - a) * m ^ (c t) * z ^ a)) :=
  odd_polynomial_correction s w n c A x z m h hA hm

example (A x z : R) (h : Commute x z) (hA : A * (x - z) = 1) (n : ℕ) :
    A * (x ^ n - z ^ n) = ∑ a ∈ range n, x ^ (n - 1 - a) * z ^ a :=
  even_correction A x z h hA n
end Generic

example (n : ℕ) :
    let x : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, -2]
    let z : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    let A : Matrix (Fin 2) (Fin 2) ℚ := !![2/3, -1/3; -1/3, -2/3]
    A * (x ^ (2 * n) - z ^ (2 * n)) =
      ∑ a ∈ range (2 * n), (-1 : ℚ) ^ a • (x ^ (2 * n - 1 - a) * z ^ a) := by
  dsimp only
  apply odd_correction_smul
  all_goals
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]

example : (let x : Matrix (Fin 2) (Fin 2) ℚ := !![2, 0; 0, -2]
    let z : Matrix (Fin 2) (Fin 2) ℚ := !![0, 1; 1, 0]
    x * z ≠ z * x) := by
  dsimp only
  intro h
  have he := congrArg (fun M => M 0 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at he

#print axioms odd_correction
#print axioms odd_correction_smul
#print axioms odd_correction_middle
#print axioms odd_polynomial_correction
#print axioms even_correction
#print axioms ordered_telescoping

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPolynomial
  let mut count : Nat := 0
  let mut privateCount : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == owner then
      for name in env.header.moduleData[i]!.constNames do
        count := count + 1
        if name.getRoot == `_private then
          privateCount := privateCount + 1
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
            throwError "Disallowed axiom {axiomName} in {name}"
  if count == 0 then
    throwError "Missing owned module {owner}"
  logInfo m!"{owner}: audited {count} declarations ({privateCount} private); standard axioms only"

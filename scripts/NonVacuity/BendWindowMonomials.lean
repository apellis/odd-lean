import OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowMonomials
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory OddMath.QuiverHecke.SwappedAssembly
namespace NonVacuity.BendWindowMonomials
private abbrev V := ModuleCat.of ℚ ℚ
private def x : Aut V where
  hom := -𝟙 V
  inv := -𝟙 V
  hom_inv_id := by simp
  inv_hom_id := by simp

-- A concrete nonzero module and its nonidentity involution.
example : (1 : ℚ) ≠ 0 := one_ne_zero
example (z : ℤ) := bend_map_aut_zpow (𝟭 (ModuleCat ℚ)) x z
example := bendFunctor_inverse (𝟭 (ModuleCat ℚ)) x
example (y : End V) (n r : ℕ) :=
  bend_evaluated_monomial (𝟭 (ModuleCat ℚ)) (𝟭 (ModuleCat ℚ))
    (𝟙 V) (𝟙 V) x y n r
end NonVacuity.BendWindowMonomials

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.SwappedAssembly.Sigma.BendWindowMonomials
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Missing owner {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned declarations"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited all {names.size} owned declarations"

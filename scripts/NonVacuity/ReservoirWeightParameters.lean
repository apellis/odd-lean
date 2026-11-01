import OddMath.QuiverHecke.ReservoirWeightParameters
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
open OddMath.QuiverHecke.ReservoirWeights
namespace NonVacuity.ReservoirWeightParameters

/-- The second original coordinate lies in the common coroot kernel. -/
private def D : SKM.Datum Unit (ℤ × ℤ) where
  cd :=
    { root := fun _ => (2, 0)
      coroot := fun _ => LinearMap.fst ℤ ℤ ℤ
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
      offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
      zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit

/-- The supplied units distinguish two weights with identical coroots. -/
private def cs : SKM.CScalars Sc where
  c μ _ := if μ.2 = 0 then 1 else -1
  shift μ i j := by
    change (if μ.2 + 0 = 0 then (1 : ℚˣ) else -1) =
      1 * (if μ.2 = 0 then 1 else -1)
    simp

example : D.h () (0, 1) = D.h () (0, 0) := rfl

example : (pairingExtensionCScalars D cs).c ((0, 1), 0) () ≠
    (pairingExtensionCScalars D cs).c ((0, 0), 0) () := by
  intro h
  have hv := congrArg (fun z : ℚˣ => (z : ℚ)) h
  norm_num [pairingExtensionCScalars, cs] at hv

example : pairingExtensionScalars D (parameterTwist D Sc) =
    parameterTwist (pairingExtension D) (pairingExtensionScalars D Sc) :=
  pairingExtensionScalars_parameterTwist D Sc

example : SKM.ipar (pairingExtension D) () ((0, 1), 0) = SKM.ipar D () (0, 1) :=
  pairingExtension_ipar_original D () (0, 1)

universe uB vB wB
variable {B : Type uB} [BicategoryStruct.{wB, vB} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]

/-- The same factor fields, including actual local inverses, restrict unchanged. -/
example (T : SKM.RouquierFamily (k := ℚ) (B := B) (pairingExtension D))
    (M : SKM.RouquierMulticolour T (pairingExtensionScalars D Sc)) :
    SKM.RouquierMulticolour (restrictRouquierFamily D T) Sc :=
  restrictRouquierMulticolour D Sc T M

end NonVacuity.ReservoirWeightParameters

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.ReservoirWeightParameters
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"

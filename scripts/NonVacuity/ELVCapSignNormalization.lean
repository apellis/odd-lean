import OddMath.QuiverHecke.CyclotomicAction.ELVCapSignNormalization
import Lean.Util.CollectAxioms
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELVOld
namespace CapSignNormalizationConsumer
private def V : SVec ℚ where
  carrier := ℚ × ℚ
  odd := (0 : (ℚ × ℚ) →ₗ[ℚ] ℚ).prod (LinearMap.snd ℚ ℚ ℚ)
  odd_comp_odd := by rfl
private def flip : V →ₗ[ℚ] V where
  toFun x := (x.2, x.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private theorem flip_odd : flip ∈ SVec.parityHom V V 1 := by
  intro q
  rcases parity_eq_zero_or_one q with rfl | rfl
  · apply LinearMap.ext
    rintro ⟨x, y⟩
    change (y - y, x - 0) = (0, x)
    simp
  · rw [SVec.zmod2_one_add_one]
    apply LinearMap.ext
    rintro ⟨x, y⟩
    change (y, 0) = (y - 0, x - x)
    simp
example : flip (1, 0) = (0, 1) := rfl
example (n : ℕ) (z : V) :
    capRowSign (k := ℚ) n • V.sgn (n : ZMod 2) ((flip.comp (V.sgn 1))^[n] z) =
      flip^[n] z :=
  capRowSign_sgn_iterate V flip flip_odd n z
example (n : ℕ) : capRowSign (k := ℚ) n = (-1 : ℚ) ^ (n * (n + 1) / 2) :=
  capRowSign_eq n
end CapSignNormalizationConsumer
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVCapSignNormalization
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing module {owner}"
  for name in env.header.moduleData[idx]!.constNames do
    for axiomName in (← Lean.collectAxioms name) do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"


import OddMath.QuiverHecke.CyclotomicAction.ProbeWordEntries
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams OddMath OddMath.QuiverHecke
namespace ProbeWordEntriesConsumer

private def D : SKM.Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
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

private def a : Unit → Polynomial ℚ := fun _ => Polynomial.X ^ 2 - 1
private abbrev s := probeBlockWord ([] : List Unit) [] ()
private abbrev C := CyclotomicWordCorner D Sc a s


example : cyclotomicWordEntry D Sc a s s (𝟙 _) =
    cyclotomicWordIdempotent D Sc a s :=
  cyclotomicWordEntry_id D Sc a s

example : cyclotomicWordIdempotent D Sc a s *
    cyclotomicWordEntry D Sc a s s (dotE D Sc s.val 0) =
    cyclotomicWordEntry D Sc a s s (dotE D Sc s.val 0) :=
  cyclotomicWordEntry_left_support D Sc a s s (dotE D Sc s.val 0)

example : (0 : C) = 0 := by
  apply cyclotomicWordEntry_distinct_kernel D Sc a s s (𝟙 _) (𝟙 _)
    (1 : C) (1 : C) (1 : C) isUnit_one isUnit_one 0 (1 : ℚ)
  · change cyclotomicWordIdempotent D Sc a s *
        cyclotomicWordIdempotent D Sc a s =
      (1 : ℚ) • (cyclotomicWordIdempotent D Sc a s *
        cyclotomicWordIdempotent D Sc a s)
    rw [one_smul]
  · change cyclotomicWordIdempotent D Sc a s *
        cyclotomicWordIdempotent D Sc a s =
      cyclotomicWordIdempotent D Sc a s +
        0 * cyclotomicWordIdempotent D Sc a s
    rw [zero_mul, add_zero]
    exact cyclotomicWordIdempotent_idem D Sc a s
  · exact mul_zero _

example : cyclotomicWordEntry D Sc a s s (𝟙 _) *
    (0 : CyclotomicAlgebra D Sc a 1) = 0 := by
  apply cyclotomicWordEntry_unit_cancel D Sc a s s (𝟙 _) (1 : C) isUnit_one
  rw [mul_zero, mul_zero]

end ProbeWordEntriesConsumer

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ProbeWordEntries
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Missing owned module {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "Empty owned module {owner}"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited {names.size} declarations in {owner}."

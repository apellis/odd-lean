import OddMath.SKM.RouquierFTriangle
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers at every integer height. The family remains a premise;
this does not construct a nonzero odd inversion model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierFTriangle
private def D : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two

example (h : ℤ) :
    (if 0 < h + 2 then (-1 : ℤ) ^ ((h + 2 - 1).toNat.choose 2)
      else -((-1 : ℤ) ^ ((-(h + 2)).toNat.choose 2))) *
    (if h < 0 then (-1 : ℤ) ^ ((-h - 1).toNat.choose 2)
      else -((-1 : ℤ) ^ (h.toNat.choose 2))) =
    koszulSign ((h + 1 : ℤ) : ZMod 2) ((h + 1 : ℤ) : ZMod 2) := by
  simpa using reflection_triangle_scalar 1 h

section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  (T : RouquierFamily (k := ℚ) (B := B) D)

example (h : ℤ) : T.leftZigF () (rfl : h + D.α () = h + D.α ()) =
    (koszulSign ((h + 1 : ℤ) : ZMod 2) ((h + 1 : ℤ) : ZMod 2) *
      (if h < 0 then 1 else -1)) • 𝟙 (T.F () rfl) := by
  simpa [leftAdjParity, D, Datum.h] using T.leftZigF_eq () (rfl : h + D.α () = _)

example : T.LeftZigzags := T.leftZigzags
example : RouquierLeftAdjoints (k := ℚ) T := T.leftAdjoints

example : T.leftZigF () (rfl : (-1 : ℤ) + D.α () = -1 + D.α ()) =
    𝟙 (T.F () rfl) := by
  have ht := T.leftZigF_eq () (rfl : (-1 : ℤ) + D.α () = _)
  norm_num [leftAdjParity, D, Datum.h, show (1 : ZMod 2) + 1 = 0 by decide] at ht
  exact ht

example : T.leftZigF () (rfl : (0 : ℤ) + D.α () = 0 + D.α ()) =
    𝟙 (T.F () rfl) := by
  have ht := T.leftZigF_eq () (rfl : (0 : ℤ) + D.α () = _)
  norm_num [leftAdjParity, D, Datum.h, show (1 : ZMod 2) + 1 = 0 by decide] at ht
  exact ht
end
end NonVacuity.RouquierFTriangle

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierFTriangle then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"

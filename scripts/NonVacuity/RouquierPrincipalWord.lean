import OddMath.SKM.RouquierPrincipalWord
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers at every integer height. The family remains a premise;
this does not construct a nonzero odd inversion model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierPrincipalWord
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

section
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  (T : RouquierFamily (k := ℚ) (B := B) D)

example (h : ℤ) :
    (T.loc () (sub_add_cancel h (D.α ())) rfl).leftCrossingWord =
      (if h ≤ 0 then 1 else (-1 : ℤ)) •
        (T.loc () (sub_add_cancel h (D.α ())) rfl).sigL := by
  simpa [D, Datum.h] using T.leftCrossingWord_eq () (sub_add_cancel h (D.α ())) rfl

example : (T.loc () (sub_add_cancel (0 : ℤ) (D.α ())) rfl).leftCrossingWord =
    (1 : ℤ) • (T.loc () (sub_add_cancel (0 : ℤ) (D.α ())) rfl).sigL := by
  simpa [D, Datum.h] using T.leftCrossingWord_eq () (sub_add_cancel (0 : ℤ) (D.α ())) rfl

example : (T.loc () (sub_add_cancel (1 : ℤ) (D.α ())) rfl).leftCrossingWord =
    (-1 : ℤ) • (T.loc () (sub_add_cancel (1 : ℤ) (D.α ())) rfl).sigL := by
  simpa [D, Datum.h] using T.leftCrossingWord_eq () (sub_add_cancel (1 : ℤ) (D.α ())) rfl

example : (T.loc () (sub_add_cancel (-1 : ℤ) (D.α ())) rfl).leftCrossingWord =
    (1 : ℤ) • (T.loc () (sub_add_cancel (-1 : ℤ) (D.α ())) rfl).sigL := by
  simpa [D, Datum.h] using T.leftCrossingWord_eq () (sub_add_cancel (-1 : ℤ) (D.α ())) rfl
end

example (h : ℤ) :
    (-1 : ℤ) * (koszulSign ((h + 1 : ℤ) : ZMod 2) ((h + 1 : ℤ) : ZMod 2) *
      (if h < 0 then 1 else -1)) * (if h ≤ 0 then 1 else -1) =
    if h = 0 then -1 else koszulSign 1 (h : ZMod 2) := by
  simpa using principalWord_scalar 1 h

example : (if (0 : ℤ) = 0 then koszulSign 1 1 else koszulSign 1 (1 * (0 : ZMod 2))) = -1 := by
  decide

end NonVacuity.RouquierPrincipalWord

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for i in [:env.header.moduleNames.size] do
    if env.header.moduleNames[i]! == `OddMath.SKM.RouquierPrincipalWord then
      for name in env.header.moduleData[i]!.constNames do
        for ax in (← Lean.collectAxioms name) do
          unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "unexpected axiom {ax} in {name}"
        count := count + 1
  if count == 0 then throwError "Empty audit"
  logInfo m!"Audited {count} owned declarations"

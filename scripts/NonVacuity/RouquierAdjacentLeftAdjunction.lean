import OddMath.SKM.RouquierAdjacentLeftAdjunction
import Lean.Util.CollectAxioms

/-! This checks the finite adjacent-local constructor against an arbitrary
rank-one Rouquier input. It does not construct a native Rouquier family. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierAdjacentLeftAdjunction
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

variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
  [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
  (T : RouquierFamily (k := ℚ) (B := B) D)

private theorem lowerEdge (h : ℤ) : (h - 2) + D.α () = h := by
  change h - 2 + 2 = h
  omega

/-- The square and braid premises are supplied by the input's actual
fields; no zigzag or additional left-adjoint premise is requested. -/
example (h : ℤ) (hh : h < 0) :
    ShiftedSuperAdjunction (k := ℚ) (T.F () (rfl : h + D.α () = _))
      (T.E () (rfl : h + D.α () = _)) (D.parity () * ((D.h () h : ZMod 2) + 1)) :=
  (T.loc () (lowerEdge h) rfl).negativeLeftAdjunction (T.loc () rfl rfl) hh
    (T.square () (lowerEdge h) rfl) (T.square () rfl rfl)
    (T.braid () (lowerEdge h) rfl rfl)

/-- The odd negative-height normalization retains a minus on the cap. -/
example :
    ((T.loc () (lowerEdge (-2)) rfl).negativeLeftAdjunction (T.loc () rfl rfl) (by decide)
      (T.square () (lowerEdge (-2)) rfl) (T.square () rfl rfl)
      (T.braid () (lowerEdge (-2)) rfl rfl)).counit =
      -(T.loc () (lowerEdge (-2)) rfl).capL := by
  rw [SuperRouquierLoc.negativeLeftAdjunction_counit]
  exact neg_one_zsmul _
end NonVacuity.RouquierAdjacentLeftAdjunction
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierAdjacentLeftAdjunction
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms"

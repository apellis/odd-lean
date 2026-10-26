import OddMath.SKM.RouquierHomSuperAdjunction
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers at arbitrary weights. The Rouquier family is an input,
not a constructed nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomSuperAdjunction
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
  [∀ a b : B, PiSupercategory ℚ (a ⟶ b)]
  (T : RouquierFamily (k := ℚ) (B := B) D) (W : ℤ → B)

example (n muM : ℤ) : SuperAdjunction (k := ℚ)
    (homContentSuperE T W () muM (muP := -(n + 2)) (nuP := -n) (by simp [D, Datum.α]))
    (homContentSuperF T W () muM (muP := -(n + 2)) (nuP := -n) (by simp [D, Datum.α])) :=
  homContentSuperAdjunction T W () muM (by simp [D, Datum.α])

example (muM muP nuP rhoP : ℤ) (h : -nuP + D.α () = -muP)
    (h₂ : -rhoP + D.α () = -nuP)
    (t : homContentSuperE T W () muM h ≫ homContentSuperE T W () muM h₂ ⟶
      homContentSuperE T W () muM h ≫ homContentSuperE T W () muM h₂)
    (Z : homWeightSector T.obj W nuP muM) :
    (rouquierMate (homContentSuperAdjunction T W () muM h)
      (homContentSuperAdjunction T W () muM h₂) t).app 1 Z =
      (homContentPreAdjunction T W T.leftAdjoints () muM h₂).unit.app
        ((homContentPreE T W () muM h).obj ((homContentPreF T W () muM h).obj Z)) ≫
      (homContentPreF T W () muM h₂).map
        (t.app 1 ((homContentPreF T W () muM h).obj Z)) ≫
      (homContentPreF T W () muM h₂).map ((homContentPreE T W () muM h₂).map
        ((homContentPreAdjunction T W T.leftAdjoints () muM h).counit.app Z)) :=
  homContentSuperAdjunction_mate_app T W () muM h h₂ t 1 Z
end NonVacuity.RouquierHomSuperAdjunction

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomSuperAdjunction] do
    let mut count : Nat := 0
    for i in [:env.header.moduleNames.size] do
      if env.header.moduleNames[i]! == mod then
        for name in env.header.moduleData[i]!.constNames do
          for ax in (← Lean.collectAxioms name) do
            unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
              throwError "unexpected axiom {ax} in {name}"
          count := count + 1
    if count == 0 then throwError "Empty audit: {mod}"
    logInfo m!"Audited {count} owned declarations in {mod}"

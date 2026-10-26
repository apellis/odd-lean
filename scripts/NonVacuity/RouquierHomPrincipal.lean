import OddMath.SKM.RouquierHomPrincipal
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers at arbitrary weights. The Rouquier family is an input,
not a constructed nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPrincipal
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

example (muM muP nuP rhoP : ℤ) (h : -nuP + D.α () = -muP)
    (h₂ : -rhoP + D.α () = -nuP)
    (Z : homWeightSector T.obj W nuP muM) :
    let P := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-nuP))
    let P₂ := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-rhoP))
    T.E () h ◁ (P.iso (T.F () h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W () muM h)
        (homContentSuperAdjunction T W () muM h₂)
        (homContentCrossing T W () muM h h₂)).app (D.parity ()) Z ≫
      (P₂.iso (T.F () h₂ ≫ T.E () h₂ ≫ Z)).hom =
    (if D.h () (-nuP) = 0 then koszulSign 1 1
      else koszulSign 1 (1 * (D.h () (-nuP) : ZMod 2))) •
      ((associator (T.E () h) (T.F () h) Z).inv ≫
        (-(T.loc () h₂ h).sigL) ▷ Z ≫
        (associator (T.F () h₂) (T.E () h₂) Z).hom) :=
  homContentCrossing_principal T W () muM h h₂ Z

theorem atHeightZero (muM : ℤ) (Z : homWeightSector T.obj W 0 muM) :
    let h : -(0 : ℤ) + D.α () = -(-2 : ℤ) := by rfl
    let h₂ : -(2 : ℤ) + D.α () = -(0 : ℤ) := by rfl
    let P := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-(0 : ℤ)))
    let P₂ := homParityShiftDatum (k := ℚ) (leftAdjParity D () (-(2 : ℤ)))
    T.E () h ◁ (P.iso (T.F () h ≫ Z)).inv ≫
      (rouquierMate (homContentSuperAdjunction T W () muM h)
        (homContentSuperAdjunction T W () muM h₂)
        (homContentCrossing T W () muM h h₂)).app (D.parity ()) Z ≫
      (P₂.iso (T.F () h₂ ≫ T.E () h₂ ≫ Z)).hom =
    (associator (T.E () h) (T.F () h) Z).inv ≫
      (T.loc () h₂ h).sigL ▷ Z ≫
      (associator (T.F () h₂) (T.E () h₂) Z).hom := by
  dsimp only
  have hh := homContentCrossing_principal T W () muM (muP := -2) (nuP := 0)
    (rhoP := 2) (by rfl) (by rfl) Z
  simpa only [show D.h () (-(0 : ℤ)) = 0 from rfl, ite_true,
    show D.parity () = 1 from rfl, koszulSign_one_one,
    TwoSupercategory.neg_whiskerRight (R := ℚ), Preadditive.comp_neg,
    Preadditive.neg_comp, neg_one_smul, neg_neg] using hh

end NonVacuity.RouquierHomPrincipal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPrincipal] do
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

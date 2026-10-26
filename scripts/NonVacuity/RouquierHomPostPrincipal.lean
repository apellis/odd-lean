import OddMath.SKM.RouquierHomPostPrincipal
import OddMath.SKM.RouquierHomPrincipal
import Lean.Util.CollectAxioms

/-! Odd rank-one consumers with odd and zero content shift. The family remains an
input; these checks apply the principal equality, not construct a nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPostPrincipal
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
  (T : ℤ → B) (W : RouquierFamily (k := ℚ) (B := B) D)
  (muP muM nuM rhoM : ℤ) (h : muM + D.α () = nuM) (h₂ : nuM + D.α () = rhoM)

example : homContentShift D () (Finsupp.single () 1) = 1 := by
  simp [homContentShift, D]

example : homContentShift D () 0 = 0 := by simp [homContentShift]

theorem oddContentPrincipal (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostSourceIso T W () (Finsupp.single () 1) muP h Z).inv ≫
      (rouquierMate (homContentPostSuperAdjunction T W () (Finsupp.single () 1) muP h)
        (homContentPostSuperAdjunction T W () (Finsupp.single () 1) muP h₂)
        (homContentPostCrossing T W () (Finsupp.single () 1) muP h h₂)).app 1 Z ≫
      (homContentPostTargetIso T W () (Finsupp.single () 1) muP h₂ Z).hom =
    (associator Z (W.F () h) (W.E () h)).hom ≫
      Z ◁ (W.loc () h h₂).sig ≫
      (associator Z (W.E () h₂) (W.F () h₂)).inv :=
  homContentPostCrossing_principal T W () (Finsupp.single () 1) muP h h₂ Z

theorem zeroContentPrincipal (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostSourceIso T W () 0 muP h Z).inv ≫
      (rouquierMate (homContentPostSuperAdjunction T W () 0 muP h)
        (homContentPostSuperAdjunction T W () 0 muP h₂)
        (homContentPostCrossing T W () 0 muP h h₂)).app 1 Z ≫
      (homContentPostTargetIso T W () 0 muP h₂ Z).hom =
    (associator Z (W.F () h) (W.E () h)).hom ≫
      Z ◁ (W.loc () h h₂).sig ≫
      (associator Z (W.E () h₂) (W.F () h₂)).inv :=
  homContentPostCrossing_principal T W () 0 muP h h₂ Z

end NonVacuity.RouquierHomPostPrincipal

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPostPrincipal] do
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
#print axioms OddMath.SKM.homContentPostCrossing_principal

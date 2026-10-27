import OddMath.SKM.RouquierHomPostInverse
import Lean.Util.CollectAxioms

/-! Actual factor-family consumers of all finite-window products and literal
parity shifts. The family is input data, not a constructed nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPostInverse
private def D (p : ZMod 2) : Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => p
  even_of_odd := fun _ _ _ => even_two
variable {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℤ (a ⟶ b)]
  [∀ a b : B, Supercategory ℤ (a ⟶ b)] [TwoSupercategory ℤ B]
  [∀ a b : B, PiSupercategory ℤ (a ⟶ b)]
  (T : ℤ → B) (muP : ℤ)

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 2) :=
  homContentPostInvPos_even T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvPos_even T W () 0 muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvNeg_even T W () 0 muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInv_zero T W () 0 muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) rfl Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 2) :=
  homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInv_zero T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (show (0 : ℤ) + (D 0).α () = 2 from rfl) rfl Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 2) :=
  homContentPostInvPos_even T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvPos_even T W () 0 muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvNeg_even T W () 0 muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInv_zero T W () 0 muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) rfl Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 2) :=
  homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) (by decide) Z

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP 0) :=
  homContentPostInv_zero T W () (Finsupp.single () 1) muP (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (show (0 : ℤ) + (D 1).α () = 2 from rfl) rfl Z


example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (2)) :=
  (homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.1 1 (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (2)) :=
  (homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.2 0 1 (by decide) (by decide) (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (2)) :=
  homContentPostInvPos_even_dotted T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide) Z 0

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (-2)) :=
  (homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.1 1 (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (-2)) :=
  (homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.2 0 1 (by decide) (by decide) (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 0))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even_dotted T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide) Z 0

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (2)) :=
  (homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.1 1 (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (2)) :=
  (homContentPostInvPos_even T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.2 0 1 (by decide) (by decide) (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (2)) :=
  homContentPostInvPos_even_dotted T W () (Finsupp.single () 1) muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide) Z 0

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (-2)) :=
  (homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.1 1 (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (-2)) :=
  (homContentPostInvNeg_even T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide) Z).2.2.2.2.2.2.2.2.2 0 1 (by decide) (by decide) (by decide)

example (W : RouquierFamily (k := ℤ) (B := B) (D 1))
    (Z : homWeightSector T W.obj muP (-2)) :=
  homContentPostInvNeg_even_dotted T W () (Finsupp.single () 1) muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide) Z 0

section Arbitrary
variable {k : Type*} [CommRing k] {C : Type*} [BicategoryStruct C]
  [∀ a b : C, Preadditive (a ⟶ b)] [∀ a b : C, Linear k (a ⟶ b)]
  [∀ a b : C, Supercategory k (a ⟶ b)] [TwoSupercategory k C]
  [∀ a b : C, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → C) (W : RouquierFamily (k := k) (B := C) D)
  (i : I) (beta : I →₀ ℕ) (muP : X) {mu nu rho : X}
  (h : mu + D.α i = nu) (h₂ : nu + D.α i = rho)
  (Z : homWeightSector T W.obj muP nu)

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).total

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).ff

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).fg

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).gf

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).gg

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).f_mem

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).g_mem

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).f'_mem

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostInvPos T W i beta muP h h₂ hh Z).g'_mem

example (hh : 0 ≤ D.h i nu) :=
  homContentPostInvPos_principal T W i beta muP h h₂ hh Z

example (hh : 0 ≤ D.h i nu) (n : ℕ) :=
  homContentPostInvPos_column T W i beta muP h h₂ hh Z n

example (hh : 0 ≤ D.h i nu) :=
  homContentPostInvPos_even_principal T W i beta muP h h₂ hh Z

example (hh : 0 ≤ D.h i nu) (n : ℕ) :=
  homContentPostInvPos_even_dotted T W i beta muP h h₂ hh Z n

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).total

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).ff

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).fg

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).gf

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).gg

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).f_mem

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).g_mem

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).f'_mem

example (hh : D.h i nu ≤ 0) :=
  (homContentPostInvNeg T W i beta muP h h₂ hh Z).g'_mem

example (hh : D.h i nu ≤ 0) :=
  homContentPostInvNeg_principal T W i beta muP h h₂ hh Z

example (hh : D.h i nu ≤ 0) (n : ℕ) :=
  homContentPostInvNeg_row T W i beta muP h h₂ hh Z n

example (hh : D.h i nu ≤ 0) :=
  homContentPostInvNeg_even_principal T W i beta muP h h₂ hh Z

example (hh : D.h i nu ≤ 0) (n : ℕ) :=
  homContentPostInvNeg_even_dotted T W i beta muP h h₂ hh Z n

example := homContentPostMate_even_to T W i beta muP h h₂ Z

example := homContentPostMate_even_from T W i beta muP h h₂ Z

example := homContentPostCap_zero T W i beta muP h Z
example := homContentPostCup_zero T W i beta muP h₂ Z
end Arbitrary
end NonVacuity.RouquierHomPostInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPostInverse] do
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
#print axioms OddMath.SKM.homContentPostInvPos
#print axioms OddMath.SKM.homContentPostInvNeg
#print axioms OddMath.SKM.homContentPostInvPos_even
#print axioms OddMath.SKM.homContentPostInvNeg_even

import OddMath.SKM.RouquierHomPostNaturalInverse
import OddMath.SKM.RouquierSupernaturalInverse
import OddMath.SKM.RouquierHomPostSuperInverse
import Lean.Util.CollectAxioms

/-! Actual factor-family consumers of all finite-window products and literal
parity shifts. The family is input data, not a constructed nonzero model. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierHomPostSuperInverse
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
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (T : ℤ → B) (muP : ℤ)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).total

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).ff

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).fg 0 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).gf 1 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).gg 0 0 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 0).α () = 2 from rfl) (show (2 : ℤ) + (D 0).α () = 4 from rfl) (by decide)).gg 0 1 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).total

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).ff

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).fg 0 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).gf 1 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).gg 0 0 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 0).α () = -2 from rfl) (show (-2 : ℤ) + (D 0).α () = 0 from rfl) (by decide)).gg 0 1 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 0)) :=
  homContentPostSuperInv_zero T W () 0 muP
    (show (-2 : ℤ) + (D 0).α () = 0 from rfl)
    (show (0 : ℤ) + (D 0).α () = 2 from rfl) (by rfl)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).total

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).ff

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).fg 0 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).gf 1 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).gg 0 0 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvPos T W () 0 muP (show (0 : ℤ) + (D 1).α () = 2 from rfl) (show (2 : ℤ) + (D 1).α () = 4 from rfl) (by decide)).gg 0 1 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).total

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).ff

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).fg 0 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).gf 1 (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).gg 0 0 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  (homContentPostSuperInvNeg T W () 0 muP (show (-4 : ℤ) + (D 1).α () = -2 from rfl) (show (-2 : ℤ) + (D 1).α () = 0 from rfl) (by decide)).gg 0 1 (by decide) (by decide)

example (W : RouquierFamily (k := k) (B := B) (D 1)) :=
  homContentPostSuperInv_zero T W () 0 muP
    (show (-2 : ℤ) + (D 1).α () = 0 from rfl)
    (show (0 : ℤ) + (D 1).α () = 2 from rfl) (by rfl)

section Arbitrary
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (beta : I →₀ ℕ) (muP : X) {mu nu rho : X}
  (h : mu + D.α i = nu) (h₂ : nu + D.α i = rho)
  {Z Z' : homWeightSector T W.obj muP nu} (f : Z ⟶ Z')
  (hf : f ∈ parity (R := k) Z Z' 1)

example (hh : 0 ≤ D.h i nu)  :=
  (homContentPostInvPos_principal_supernatural T W i beta muP h h₂ hh).naturality hf

example (hh : D.h i nu ≤ 0)  :=
  (homContentPostInvNeg_principal_supernatural T W i beta muP h h₂ hh).naturality hf

example (hh : 0 ≤ D.h i nu) (n : ℕ) :=
  (homContentPostInvPos_column_supernatural T W i beta muP h h₂ hh n).naturality hf

example (hh : D.h i nu ≤ 0) (n : ℕ) :=
  (homContentPostInvNeg_row_supernatural T W i beta muP h h₂ hh n).naturality hf

example  :=
  (homContentPostEvenMateTo T W i beta muP h h₂).naturality f

example  :=
  (homContentPostEvenMateFrom T W i beta muP h h₂).naturality f

example (n : ℕ) :=
  (homContentPostEvenCap T W i beta muP h n).naturality f

example (n : ℕ) :=
  (homContentPostEvenCup T W i beta muP h₂ n).naturality f

example (hh : 0 ≤ D.h i nu) :=
  (homContentPostEvenInvPosPrincipal T W i beta muP h h₂ hh).naturality f

example (hh : 0 ≤ D.h i nu) (n : ℕ) :=
  (homContentPostEvenInvPosColumn T W i beta muP h h₂ hh n).naturality f

example (hh : D.h i nu ≤ 0) :=
  (homContentPostEvenInvNegPrincipal T W i beta muP h h₂ hh).naturality f

example (hh : D.h i nu ≤ 0) (n : ℕ) :=
  (homContentPostEvenInvNegRow T W i beta muP h h₂ hh n).naturality f

example (hh : 0 ≤ D.h i nu) := homContentPostEvenInvPos_products T W i beta muP h h₂ hh
example (hh : D.h i nu ≤ 0) := homContentPostEvenInvNeg_products T W i beta muP h h₂ hh
example (n : ℕ) (q : ZMod 2) := homContentPostSuperCap_app T W i beta muP h n q Z
example (n : ℕ) (q : ZMod 2) := homContentPostSuperCup_app T W i beta muP h₂ n q Z
example (hh : 0 ≤ D.h i nu) (n : ℕ) (q : ZMod 2) :=
  homContentPostSuperInvPos_column_app T W i beta muP h h₂ hh n q Z
example (hh : D.h i nu ≤ 0) (n : ℕ) (q : ZMod 2) :=
  homContentPostSuperInvNeg_row_app T W i beta muP h h₂ hh n q Z
example := (homContentPostMate_supernatural T W i beta muP h h₂).naturality hf
example (n : ℕ) := (homContentPostCap_supernatural T W i beta muP h n).naturality hf
example (n : ℕ) := (homContentPostCup_supernatural T W i beta muP h₂ n).naturality hf
example (n : ℕ) := (homContentPostDot_power_supernatural T W i beta muP h₂ n).naturality hf
example := homContentPostSuperMate_eq T W i beta muP h h₂
end Arbitrary
end NonVacuity.RouquierHomPostSuperInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for mod in #[`OddMath.SKM.RouquierHomPostNaturalInverse,
      `OddMath.SKM.RouquierSupernaturalInverse, `OddMath.SKM.RouquierHomPostSuperInverse] do
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
#print axioms OddMath.SKM.homContentPostSuperInvPos
#print axioms OddMath.SKM.homContentPostSuperInvNeg

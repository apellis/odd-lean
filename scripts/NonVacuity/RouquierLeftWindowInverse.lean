import OddMath.SKM.RouquierLeftWindowInverse
import OddMath.SKM.RouquierHomPostSuperInverse
import OddMath.SKM.RouquierHomPrincipal
import OddMath.SKM.RouquierHomReservoirPowers
import Lean.Util.CollectAxioms

/-! The specified local factor inverse is input data, not a constructed nonzero
model. Both parities, both nonempty windows, and the empty height-zero boundary
are consumed without triangularity or inverse-window hypotheses. -/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace NonVacuity.RouquierLeftWindowInverse
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (1)) := L.leftWindowCup_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (1)) := L.leftCupTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (1)) := L.leftCupTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (1)) (n : Fin 1) := L.leftWindowCupRow_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (1)) (n : ℕ) := L.leftWindowCup_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (3)) := L.leftWindowCup_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (3)) := L.leftCupTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (3)) := L.leftCupTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (3)) (n : Fin 3) := L.leftWindowCupRow_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (3)) (n : ℕ) := L.leftWindowCup_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1)) := L.leftWindowCap_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1)) := L.leftCapTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1)) := L.leftCapTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1)) (n : Fin 1) := L.leftWindowCapColumn_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-1)) (n : ℕ) := L.leftWindowCap_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-3)) := L.leftWindowCap_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-3)) := L.leftCapTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-3)) := L.leftCapTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-3)) (n : Fin 3) := L.leftWindowCapColumn_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (-3)) (n : ℕ) := L.leftWindowCap_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 0 (0)) := L.leftWindow_zero_inverse rfl

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (1)) := L.leftWindowCup_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (1)) := L.leftCupTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (1)) := L.leftCupTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (1)) (n : Fin 1) := L.leftWindowCupRow_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (1)) (n : ℕ) := L.leftWindowCup_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (3)) := L.leftWindowCup_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (3)) := L.leftCupTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (3)) := L.leftCupTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (3)) (n : Fin 3) := L.leftWindowCupRow_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (3)) (n : ℕ) := L.leftWindowCup_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) := L.leftWindowCap_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) := L.leftCapTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) := L.leftCapTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) (n : Fin 1) := L.leftWindowCapColumn_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-1)) (n : ℕ) := L.leftWindowCap_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) := L.leftWindowCap_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) := L.leftCapTransition_inverse (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) := L.leftCapTransition_nilpotent (by decide)
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) (n : Fin 3) := L.leftWindowCapColumn_mem (by decide) n
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (-3)) (n : ℕ) := L.leftWindowCap_mem n

example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t 1 (0)) := L.leftWindow_zero_inverse rfl

section AllHeights
variable {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)
example (hh : 0 < h) := L.leftWindowCup_inverse hh
example (hh : h < 0) := L.leftWindowCap_inverse hh
example (hh : h = 0) := L.leftWindow_zero_inverse hh
example (hh : 0 < h) (n : Fin h.toNat) := L.leftWindowCupRow_mem hh n
example (hh : h < 0) (n : Fin (-h).toNat) := L.leftWindowCapColumn_mem hh n
example (hh : 0 < h) (n : ℕ) (hn : n < h.toNat) := L.leftWindowCup_expansion hh hn
example (hh : h < 0) (n : ℕ) (hn : n < (-h).toNat) := L.leftWindowCap_expansion hh hn
end AllHeights
end NonVacuity.RouquierLeftWindowInverse

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mod := `OddMath.SKM.RouquierLeftWindowInverse
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
#print axioms OddMath.SKM.SuperRouquierLoc.leftWindowCup_inverse
#print axioms OddMath.SKM.SuperRouquierLoc.leftWindowCap_inverse
#print axioms OddMath.SKM.SuperRouquierLoc.leftWindow_zero_inverse
#print axioms OddMath.SKM.SuperRouquierLoc.leftWindowCupRow_mem
#print axioms OddMath.SKM.SuperRouquierLoc.leftWindowCapColumn_mem

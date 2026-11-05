/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.RouquierData

/-! # Natural-number profiles of augmented inverses

BE (1.13)–(1.14): finite module inverses use the shift profile `n • p`,
while the Rouquier local-action presentation uses `(n : ZMod 2) * p`.
This conversion retains every chosen inverse map literally. It is needed
by the content-grid and weight-product local-action constructions.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM
universe u v w
variable {k : Type w} [CommRing k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : C} {p : ZMod 2} {n : ℕ}

/-- Change only the shift-profile notation in a column inverse. -/
def SuperSumInvFrom.mulProfile {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p (fun m => m • p) n) :
    SuperSumInvFrom (k := k) f g p (fun m => (m : ZMod 2) * p) n where
  f' := J.f'
  g' := J.g'
  f_mem := J.f_mem
  g_mem m := by simpa only [nsmul_eq_mul] using J.g_mem m
  f'_mem := J.f'_mem
  g'_mem m := by simpa only [nsmul_eq_mul] using J.g'_mem m
  total := J.total
  ff := J.ff
  fg := J.fg
  gf := J.gf
  gg := J.gg

/-- Change only the shift-profile notation in a row inverse. -/
def SuperSumInvTo.mulProfile {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p (fun m => m • p) n) :
    SuperSumInvTo (k := k) f g p (fun m => (m : ZMod 2) * p) n where
  f' := J.f'
  g' := J.g'
  f_mem := J.f_mem
  g_mem m := by simpa only [nsmul_eq_mul] using J.g_mem m
  f'_mem := J.f'_mem
  g'_mem m := by simpa only [nsmul_eq_mul] using J.g'_mem m
  total := J.total
  ff := J.ff
  fg := J.fg
  gf := J.gf
  gg := J.gg

@[simp] theorem SuperSumInvFrom.mulProfile_f' {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p (fun m => m • p) n) : J.mulProfile.f' = J.f' := rfl
@[simp] theorem SuperSumInvFrom.mulProfile_g' {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p (fun m => m • p) n) (m : ℕ) :
    J.mulProfile.g' m = J.g' m := rfl
@[simp] theorem SuperSumInvTo.mulProfile_f' {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p (fun m => m • p) n) : J.mulProfile.f' = J.f' := rfl
@[simp] theorem SuperSumInvTo.mulProfile_g' {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p (fun m => m • p) n) (m : ℕ) :
    J.mulProfile.g' m = J.g' m := rfl

end OddMath.SKM

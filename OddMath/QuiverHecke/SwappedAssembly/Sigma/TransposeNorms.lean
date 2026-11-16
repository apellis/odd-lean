/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Generators.CrossCoeffExistence
import OddMath.SKM.RouquierHomPostInverseUnits

/-! # Source denominator norms for the reservoir mixed mate

These are the three literal source-unit inputs of the post-side mixed mate.
They require no common nilpotence exponent on a reservoir weight fibre.
The previous whole-dot unit/nilpotence hypotheses remain sufficient.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe r u v w

section Source
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B} (E : a ⟶ b) {E' : c ⟶ d} {F' : d ⟶ c}
  (A : SuperAdjunction (k := k) E' F') (κ : ZMod 2) (H : b ⟶ d)

/-- The source pre dot is a functorial image of the probe dot. -/
theorem mixedPostSourcePreDot_isUnit {x : End E} (hu : IsUnit x) :
    IsUnit (mixedPostSourcePreDot (k := k) E κ H (F' := F') x) :=
  hu.map ((homPost (k := k) ((homParityShift (k := k) κ).obj H ≫ F')).mapEnd E)

end Source
end OddMath.SKM

namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- Literal transposed source norms, independently of any whole-fibre dot exponent. -/
structure CrossTransposeNormUnits : Prop where
  even : ∀ (i : I), D.parity i = 0 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) -
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW))
  odd_sub : ∀ (i : I), D.parity i = 1 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) ^ 2 -
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW) ^ 2)
  odd_add : ∀ (i : I), D.parity i = 1 → ∀ {xP yP xW yW : X}
    (hP : xP + D.α i = yP) (hW : xW + D.α i = yW) (κ : ZMod 2)
    (H : P.T.obj yP ⟶ P.W.obj yW),
    IsUnit (mixedPostSourcePreDot (k := k) (P.T.E i hP) κ H (F' := P.W.F i hW) (P.T.dot i hP) ^ 2 +
      mixedPostSourcePostDot (k := k) (P.T.E i hP) κ H (P.W.adj i hW) (P.W.dot i hW) ^ 2)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunctionCounit

/-!
# The cyclotomic super adjunction

Ports the induction-restriction adjunction of
`Categorification/TwoRep/CyclotomicRouqAdjunction.lean` to the actual
cyclotomic supermodule categories. The unit and counit are even and their
naturality includes odd morphisms.
-/

noncomputable section
open CategoryTheory StringDiagrams
open SuperBimodule
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
variable (i : I) (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a) (n : ℕ)
local notation "φ" => cyclotomicAppend D Sc i a n
local notation "P" => inductionCorner D Sc i a ha n
local notation "Q" => restrictionCorner D Sc i a ha n
local notation "F" => cyclotomicSuperInduction D Sc i a ha n
local notation "E" => cyclotomicSuperRestriction D Sc i a ha n

theorem superInduction_triangle (M : CyclotomicSupermodules D Sc a ha n) :
    (F).map ((cyclotomicSuperUnit D Sc i a ha n).app M) ≫
      (cyclotomicSuperCounit D Sc i a ha n).app ((F).obj M) = 𝟙 ((F).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext P M
  intro x m
  change superCounitLinear D Sc i a ha n (tensor P M)
    ((whiskerLeft P (superUnitComponent D Sc i a ha n M)).1 (btmul P M x m)) = btmul P M x m
  rw [whiskerLeft_btmul_even P _ (superUnitComponent_mem D Sc i a ha n M)]
  change superCounitLinear D Sc i a ha n (tensor P M)
    (btmul P (tensor Q (tensor P M)) x
      (btmul Q (tensor P M) (restrictionCornerOf D Sc i a ha n 1)
        (btmul P M (inductionCornerIdempotent D Sc i a ha n) m))) = btmul P M x m
  rw [superCounitLinear_btmul_btmul, lact_btmul]
  congr 1
  apply Subtype.ext
  change (x.1 * φ 1) * φ 1 = x.1
  rw [x.2, x.2]

theorem superRestriction_triangle (M : CyclotomicSupermodules D Sc a ha (n + 1)) :
    (cyclotomicSuperUnit D Sc i a ha n).app ((E).obj M) ≫
      (E).map ((cyclotomicSuperCounit D Sc i a ha n).app M) = 𝟙 ((E).obj M) := by
  apply SuperBimodule.hom_ext
  apply tensor_hom_ext Q M
  intro y m
  change (whiskerLeft Q (superCounitComponent D Sc i a ha n M)).1
    (superUnitLinear D Sc i a ha n (tensor Q M) (btmul Q M y m)) = btmul Q M y m
  rw [superUnitLinear_apply,
    whiskerLeft_btmul_even Q _ (superCounitComponent_mem D Sc i a ha n M)]
  change btmul Q M (restrictionCornerOf D Sc i a ha n 1)
    (superCounitLinear D Sc i a ha n M
      (btmul P (tensor Q M) (inductionCornerIdempotent D Sc i a ha n) (btmul Q M y m))) =
    btmul Q M y m
  rw [superCounitLinear_btmul_btmul]
  change btmul Q M (restrictionCornerOf D Sc i a ha n 1) (M.lact (φ 1 * y.1) m) = btmul Q M y m
  rw [y.2, ← btmul_ract_lact]
  congr 1
  apply Subtype.ext
  exact y.2

end OddMath.QuiverHecke

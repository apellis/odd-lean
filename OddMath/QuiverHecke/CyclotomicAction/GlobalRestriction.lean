/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction

/-!
# Restriction and adjunction on content supercategories

Ports the block restriction and adjunction used by
`Categorification/KLR/CyclotomicAction/Global.lean`. These are the genuine
balanced-tensor functors on full content supercategories, including odd
module morphisms. The restriction corner intertwines the two central content
projectors, so the usual even unit and counit restrict without modification.
The height-zero boundary and the product over weight blocks are not asserted.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.CyclotomicAction
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k) [Fintype I]
  (a : I → _root_.Polynomial k) (ha : CyclotomicPolynomialParity D a)
  (i : I) (n : ℕ) (β : Multiset I)

/-- On the restriction corner the lower projector equals the upper projector. -/
theorem restrictionCorner_content (x : (restrictionCorner D Sc i a ha n).toSVec) :
    (restrictionCorner D Sc i a ha n).lact
        (cyclotomicContentIdempotent D Sc a n β) x =
      (restrictionCorner D Sc i a ha n).ract
        (cyclotomicContentIdempotent D Sc a (n + 1) ({i} + β)) x := by
  apply Subtype.ext
  change cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β) * x.1 =
    x.1 * cyclotomicContentIdempotent D Sc a (n + 1) ({i} + β)
  have he := cyclotomicContentIdempotent_append D Sc i a n β 1
  rw [mul_one] at he
  rw [← he, mul_assoc, x.2, cyclotomicContentIdempotent_central]

/-- Balanced-tensor restriction removes the selected colour from content. -/
theorem contentSupported_restriction (M : CyclotomicSupermodules D Sc a ha (n + 1))
    (hM : ContentSupported D Sc a ha (n + 1) ({i} + β) M) :
    ContentSupported D Sc a ha n β ((cyclotomicSuperRestriction D Sc i a ha n).obj M) := by
  intro z
  change (SuperBimodule.tensor (restrictionCorner D Sc i a ha n) M).lact _ z = z
  induction z using SuperBimodule.tensor_induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | btmul x m =>
    rw [SuperBimodule.lact_btmul, restrictionCorner_content,
      SuperBimodule.btmul_ract_lact, hM m]

/-- The concrete restriction superfunctor on the two content blocks. -/
def globalBlockRestriction :
    Superfunctor k (CyclotomicContentModules D Sc a ha (n + 1) ({i} + β))
      (CyclotomicContentModules D Sc a ha n β) := by
  let P : ObjectProperty (CyclotomicSupermodules D Sc a ha (n + 1)) :=
    ContentSupported D Sc a ha (n + 1) ({i} + β)
  let Q : ObjectProperty (CyclotomicSupermodules D Sc a ha n) := ContentSupported D Sc a ha n β
  change Superfunctor k P.FullSubcategory Q.FullSubcategory
  apply fullLiftSuperfunctor P Q ⟨cyclotomicSuperRestriction D Sc i a ha n⟩
  intro M hM
  exact contentSupported_restriction D Sc a ha i n β M hM

local notation "F" => globalBlockInduction D Sc a ha i n β
local notation "E" => globalBlockRestriction D Sc a ha i n β

/-- The even induction–restriction adjunction restricted to full content blocks. -/
def globalBlockAdjunction : (F).toFunctor ⊣ (E).toFunctor := by
  let P : ObjectProperty (CyclotomicSupermodules D Sc a ha n) := ContentSupported D Sc a ha n β
  let Q : ObjectProperty (CyclotomicSupermodules D Sc a ha (n + 1)) := ContentSupported D Sc a ha (n + 1) ({i} + β)
  exact fullLiftAdjunction P Q (cyclotomicSuperInduction D Sc i a ha n)
    (cyclotomicSuperRestriction D Sc i a ha n)
    (contentSupported_induction D Sc a ha i n β)
    (contentSupported_restriction D Sc a ha i n β)
    (cyclotomicSuperIndResAdjunction D Sc i a ha n)

/-- The original even unit, restricted to the source content. -/
def globalBlockUnit : 𝟭 (CyclotomicContentModules D Sc a ha n β) ⟶ (F).toFunctor ⋙ (E).toFunctor :=
  (globalBlockAdjunction D Sc a ha i n β).unit

/-- The original even counit, restricted to the target content. -/
def globalBlockCounit : (E).toFunctor ⋙ (F).toFunctor ⟶
    𝟭 (CyclotomicContentModules D Sc a ha (n + 1) ({i} + β)) :=
  (globalBlockAdjunction D Sc a ha i n β).counit

theorem globalBlockUnit_mem (M : CyclotomicContentModules D Sc a ha n β) :
    (globalBlockUnit D Sc a ha i n β).app M ∈ parity (R := k) _ _ 0 :=
  superUnitComponent_mem D Sc i a ha n M.obj

theorem globalBlockCounit_mem
    (M : CyclotomicContentModules D Sc a ha (n + 1) ({i} + β)) :
    (globalBlockCounit D Sc a ha i n β).app M ∈ parity (R := k) _ _ 0 :=
  superCounitComponent_mem D Sc i a ha n M.obj

end OddMath.QuiverHecke.CyclotomicAction

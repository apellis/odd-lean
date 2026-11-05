/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.GlobalSupport
import OddMath.QuiverHecke.CyclotomicAction.SuperAdjunction

/-!
# Restriction and adjunction on content supercategories

Ports the block restriction and adjunction (`resBlock`, `globalAdj` on one
block) of `Categorification/KLR/CyclotomicAction/Global.lean`. These are the
balanced-tensor functors on full content supercategories, including odd
module morphisms. The restriction corner intertwines the two central content
projectors, so the even unit and counit of `cyclotomicSuperIndResAdjunction`
restrict without modification. Only positive heights are treated here: the
restriction from one strand to the empty word is not constructed.
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
        (cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)) x := by
  apply Subtype.ext
  change cyclotomicAppend D Sc i a n (cyclotomicContentIdempotent D Sc a n β) * x.1 =
    x.1 * cyclotomicContentIdempotent D Sc a (n + 1) (({i} : Multiset I) + β)
  have he := cyclotomicContentIdempotent_append D Sc i a n β 1
  rw [mul_one] at he
  rw [← he, mul_assoc, x.2, cyclotomicContentIdempotent_central]

/-- Balanced-tensor restriction removes the selected colour from content. -/
theorem contentSupported_restriction (M : CyclotomicSupermodules D Sc a ha (n + 1))
    (hM : ContentSupported D Sc a ha (n + 1) (({i} : Multiset I) + β) M) :
    ContentSupported D Sc a ha n β ((cyclotomicSuperRestriction D Sc i a ha n).obj M) := by
  intro z
  change (SuperBimodule.tensor (restrictionCorner D Sc i a ha n) M).lact _ z = z
  induction z using SuperBimodule.tensor_induction_on with
  | zero => exact map_zero _
  | add x y hx hy => rw [map_add, hx, hy]
  | btmul x m =>
    rw [SuperBimodule.lact_btmul, restrictionCorner_content,
      SuperBimodule.btmul_ract_lact, hM m]

end OddMath.QuiverHecke.CyclotomicAction

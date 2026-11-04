import OddMath.SKM.RouquierHomPreMateSlide
import OddMath.SKM.RouquierHomBendMonomials

/-! # Literal probe slide and nonnegative automorphism windows

SwappedHomInversion §2 (1): extract the pointwise slide of the prescribed
normalized precomposition mate and retain its actual raw probe dot. The
nonnegative windows use the same automorphisms as the separated mixed
bends in §3, without introducing another probe model.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP rhoP : X}
  (h : -nuP + D.α i = -muP) (h₂ : -rhoP + D.α i = -nuP)

/-- The actual normalized mate, raw source dot, lowered target dot, cap
and unit satisfy the slide on every Hom object at every factor height. -/
theorem homContentPreMate_slide_app (Z : homWeightSector T.obj W nuP muM) :
    homContentPreMate T W i muM h h₂ Z ≫
        (homContentPreF T W i muM h₂).map (homReservoirDot T W i muM h₂ Z) -
      koszulSign (D.parity i) (D.parity i) •
        (homReservoirDot T W i muM h ((homContentPreF T W i muM h).obj Z) ≫
          homContentPreMate T W i muM h h₂ Z) =
      (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z ≫
        (homContentPreAdjunction T W T.leftAdjoints i muM h₂).unit.app Z := by
  have H := congrArg (fun f => f.app 0 Z) (homContentPreMate_slide T W i muM h h₂)
  rw [← homContentPreSuperMate_eq] at H
  rcases parity_eq_zero_or_one (D.parity i) with hp | hp
  all_goals simpa [sub_eq_add_neg, SCat.comp_app_zero, SCat.whiskerLeft_app,
    SCat.whiskerRight_app, homContentPreSuperMate, IsSupernatural.toSuperNatTrans,
    homContentPreSuperDot,
    homPreTransform, homContentSuperAdjunction, superAdjunctionOfEven,
    SuperNatTrans.ofNatTrans, homContentSuperE, homContentSuperF,
    Superfunctor.obj, Superfunctor.map, hp, homReservoirDot,
    homContentPreE, homContentPreF, Functor.comp_obj, Functor.comp_map] using H

/-- Any additive output evaluation preserves the actual pointwise slide. -/
theorem homContentPreMate_slide_map {C : Type*} [Category C] [Preadditive C]
    (E : homWeightSector T.obj W nuP muM ⥤ C) [E.Additive]
    (Z : homWeightSector T.obj W nuP muM) :
    E.map (homContentPreMate T W i muM h h₂ Z) ≫
        E.map ((homContentPreF T W i muM h₂).map (homReservoirDot T W i muM h₂ Z)) -
      koszulSign (D.parity i) (D.parity i) •
        (E.map (homReservoirDot T W i muM h ((homContentPreF T W i muM h).obj Z)) ≫
          E.map (homContentPreMate T W i muM h h₂ Z)) =
      E.map ((homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z) ≫
        E.map ((homContentPreAdjunction T W T.leftAdjoints i muM h₂).unit.app Z) := by
  simpa only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp] using
    congrArg E.map (homContentPreMate_slide_app T W i muM h h₂ Z)

end OddMath.SKM

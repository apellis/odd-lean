import OddMath.Frontier.EQHalfGradedUnitParity

/-!
# Integral unit restriction and the actual module parity involution

At every rank, restriction along the integral unit intertwines the existing
module parity involutions, both defined by the inverse periodic unit. The
comparison uses the module-level composition and shift comparisons underlying
`restrictParityIso`; neither parity functor nor involution is transported.
-/

noncomputable section
universe w
namespace OddMath.Frontier.EQHalfGradedUnit
open CategoryTheory DG

/-- The integral unit preserves the inverse periodic unit as an actual weight morphism. -/
theorem weightFunctor_map_unitInvHom (N : ℕ)
    (i j : WeightCategory source.Regraded) (h : j.as = i.as + 2 * (2 : ℤ)) :
    (weightFunctor N).map (HalfGradedDGRing.unitInvHom source i j h) =
      HalfGradedDGRing.unitInvHom (target N) ((weightFunctor N).obj i)
        ((weightFunctor N).obj j) h := by
  apply Subtype.ext
  exact regradedHom_periodUnitInv N

/-- Module restriction commutes with internal shift by the actual composition comparisons. -/
def precompInternalShiftIso (N : ℕ) (s : ℤ) :
    CatModule.precomp.{w} (weightFunctor N) ⋙
        HalfGradedDGRing.internalShiftFunctor source s ≅
      HalfGradedDGRing.internalShiftFunctor (target N) s ⋙
        CatModule.precomp (weightFunctor N) :=
  (CatModule.precompCompIso
    (WeightCategory.shiftFunctor source.Regraded s) (weightFunctor N)).symm ≪≫
  CatModule.precompCompIso (weightFunctor N)
    (WeightCategory.shiftFunctor (target N).Regraded s)

/-- The module counterpart of `restrictParityIso`, with the same actual comparisons. -/
def precompParityIso (N : ℕ) :
    CatModule.precomp.{w} (weightFunctor N) ⋙ HalfGradedDGRing.parityShift source ≅
      HalfGradedDGRing.parityShift (target N) ⋙ CatModule.precomp (weightFunctor N) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (precompInternalShiftIso N (-2)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      ((CatModule.precomp (weightFunctor N)).commShiftIso (1 : ℤ)).symm ≪≫
    (Functor.associator _ _ _).symm

/-- Restriction intertwines the two actual module involutions in every rank. -/
theorem precompParityIso_involution (N : ℕ)
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    (HalfGradedDGRing.parityShift source).map ((precompParityIso N).hom.app M) ≫
        (precompParityIso N).hom.app ((HalfGradedDGRing.parityShift (target N)).obj M) ≫
        (CatModule.precomp (weightFunctor N)).map
          ((HalfGradedDGRing.parityShiftIso (target N)).hom.app M) =
      (HalfGradedDGRing.parityShiftIso source).hom.app
        ((CatModule.precomp (weightFunctor N)).obj M) := by
  apply CatModule.hom_ext
  intro i m
  change M.act (HalfGradedDGRing.unitInvHom (target N) _ _ _) _ =
    M.act ((weightFunctor N).map (HalfGradedDGRing.unitInvHom source _ _ _)) _
  rw [weightFunctor_map_unitInvHom]

/-- Apply the actual parity comparison twice, without changing either involution. -/
def precompParityTwiceIso (N : ℕ) :
    CatModule.precomp.{w} (weightFunctor N) ⋙
        (HalfGradedDGRing.parityShift source ⋙ HalfGradedDGRing.parityShift source) ≅
      (HalfGradedDGRing.parityShift (target N) ⋙
        HalfGradedDGRing.parityShift (target N)) ⋙ CatModule.precomp (weightFunctor N) :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (precompParityIso N) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (precompParityIso N) ≪≫
    (Functor.associator _ _ _).symm

/-- Natural-isomorphism form of the actual involution square, ready for localization. -/
theorem precompParityIso_involution_natIso (N : ℕ) :
    precompParityTwiceIso.{w} N ≪≫
        Functor.isoWhiskerRight (HalfGradedDGRing.parityShiftIso (target N))
          (CatModule.precomp (weightFunctor N)) ≪≫
        Functor.leftUnitor (CatModule.precomp (weightFunctor N)) =
      Functor.isoWhiskerLeft (CatModule.precomp (weightFunctor N))
          (HalfGradedDGRing.parityShiftIso source) ≪≫
        Functor.rightUnitor (CatModule.precomp (weightFunctor N)) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simpa [precompParityTwiceIso] using precompParityIso_involution N M

universe wS

/-- The same square after the actual source localization functor `Q`.
The localization universe is independent of the module universe; no low-rank
hypothesis, equivalence, or transported involution is used. This is not yet the
coherence of `restrictParityIso`: identifying its `Q`-whiskering remains necessary. -/
theorem Q_map_precompParityIso_involution (N : ℕ)
    [CatModule.HasDerivedCategory.{wS, w} (WeightCategory source.Regraded)]
    (M : CatModule.{w} (WeightCategory (target N).Regraded)) :
    CatModule.DerivedCategory.Q.map
        ((HalfGradedDGRing.parityShift source).map ((precompParityIso N).hom.app M)) ≫
      CatModule.DerivedCategory.Q.map
        ((precompParityIso N).hom.app ((HalfGradedDGRing.parityShift (target N)).obj M)) ≫
      CatModule.DerivedCategory.Q.map
        ((CatModule.precomp (weightFunctor N)).map
          ((HalfGradedDGRing.parityShiftIso (target N)).hom.app M)) =
      CatModule.DerivedCategory.Q.map
        ((HalfGradedDGRing.parityShiftIso source).hom.app
          ((CatModule.precomp (weightFunctor N)).obj M)) := by
  simpa only [Functor.map_comp] using
    congrArg (CatModule.DerivedCategory.Q.map) (precompParityIso_involution N M)

end OddMath.Frontier.EQHalfGradedUnit

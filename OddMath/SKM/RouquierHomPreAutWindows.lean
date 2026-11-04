import OddMath.SKM.RouquierHomBendMonomials

/-! # Nonnegative normalized probe windows as automorphism powers

The nonnegative row and column data of SwappedHomInversion §2 use the
same raw probe automorphisms as the negative windows in §3. These
equalities retain the specified normalized precomposition adjunction.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

/-- Additive output evaluation retains integral powers of the specified
automorphism. The equality also applies to negative window exponents. -/
theorem map_aut_zpow_hom {C C' : Type*} [Category C] [Category C']
    (L : C ⥤ C') {Z : C} (a : Aut Z) (n : ℤ) :
    L.map (a ^ n).hom = (Functor.mapAut Z L a ^ n).hom := by
  rw [← map_zpow]
  rfl

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D)
  (i : I) {a b m : X} (h : -b + D.α i = -a)
  [IsIso (T.dot i h)]

/-- Every nonnegative cap is the prescribed source automorphism power
followed by the prescribed normalized counit. -/
theorem homReservoirCap_aut (n : ℕ) (Z : homWeightSector T.obj W.obj b m) :
    homReservoirCap T W.obj i m h n Z =
      (homPreDotAut T W i h ((homContentPreF T W.obj i m h).obj Z) ^ (n : ℤ)).hom ≫
        homReservoirCap T W.obj i m h 0 Z := by
  simp only [homReservoirCap, pow_zero, End.one_def, Category.id_comp]
  change _ = Aut.toEnd _ (homPreDotAut T W i h _ ^ (n : ℤ)) ≫ _
  rw [zpow_natCast, map_pow]
  rfl

/-- Every nonnegative unit is the prescribed normalized unit followed
by the probe automorphism power under its actual shifted right adjoint. -/
theorem homReservoirCup_aut (n : ℕ) (Z : homWeightSector T.obj W.obj a m) :
    homReservoirCup T W.obj i m h n Z =
      homReservoirCup T W.obj i m h 0 Z ≫
        (Functor.mapAut _ (homContentPreF T W.obj i m h) (homPreDotAut T W i h Z) ^
          (n : ℤ)).hom := by
  have hzero : homReservoirCup T W.obj i m h 0 Z =
      (homContentPreAdjunction T W.obj T.leftAdjoints i m h).unit.app Z := by
    simpa only [homReservoirCup, pow_zero, End.one_def,
      (homContentPreF T W.obj i m h).map_id, Functor.comp_obj] using
      Category.comp_id ((homContentPreAdjunction T W.obj T.leftAdjoints i m h).unit.app Z)
  rw [hzero, homReservoirCup, ← map_aut_zpow_hom]
  congr 2
  change _ = Aut.toEnd _ (homPreDotAut T W i h Z ^ (n : ℤ))
  rw [zpow_natCast, map_pow]
  rfl

end OddMath.SKM

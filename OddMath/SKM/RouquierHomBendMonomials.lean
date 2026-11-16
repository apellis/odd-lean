import OddMath.SKM.RouquierHomPreNegativePowers
import OddMath.SKM.RouquierHomPostNaturalInverse

/-!
# Separation of the dotted mixed-bend monomials

`SwappedHomInversion.md` §3 (4)–(6): the ordered monomials inside a mixed
bend separate into the prescribed negative probe window and nonnegative
reservoir window. Consecutive exponents have zero parity product. The
adjunctions, shifts and inverse probe dot are the specified Hom-sector
ones, and the input Hom object is arbitrary.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Automorphisms
variable {C C' : Type*} [Category C] [Category C']

/-- The inverse homomorphism of an automorphism, in its endomorphism monoid. -/
def autInverseEnd {Z : C} (a : Aut Z) : End Z := a.inv

/-- Negative integral powers of an automorphism are natural powers of
its inverse endomorphism, with the chronological endomorphism convention. -/
theorem aut_inv_power_eq_zpow {Z : C} (a : Aut Z) (n : ℕ) :
    autInverseEnd a ^ n = (a ^ (-(n : ℤ))).hom := by
  change (Aut.toEnd Z (a⁻¹)) ^ n = Aut.toEnd Z (a ^ (-(n : ℤ)))
  rw [zpow_neg, zpow_natCast, ← inv_pow, map_pow]

/-- Output evaluation preserves the same negative probe automorphism,
including on arbitrary modules and zero corners. -/
theorem map_aut_inv_power_eq_zpow (F : C ⥤ C') {Z : C} (a : Aut Z) (n : ℕ) :
    F.map (autInverseEnd a ^ n) = (Functor.mapAut Z F a ^ (-(n : ℤ))).hom := by
  rw [← aut_inv_power_eq_zpow]
  exact map_pow (Functor.mapEnd Z F) (autInverseEnd a) n

end Automorphisms

private theorem consecutive_parity (p : ZMod 2) (n : ℕ) :
    (n * p) * ((n + 1 : ℕ) * p) = 0 := by
  push_cast
  generalize (n : ZMod 2) = a
  fin_cases a <;> fin_cases p <;> decide

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D)
  (i : I) (β : I →₀ ℕ) {a b m n : X}
  (hP : -b + D.α i = -a) (hR : m + D.α i = n)
  [IsIso (T.dot i hP)]

/-- The prescribed probe dot, with its whiskered inverse, as an
automorphism. This does not choose an inverse from a coefficient formula. -/
def homPreDotAut (Z : homWeightSector T.obj W.obj a m) :
    Aut ((homContentPreE T W.obj i m hP).obj Z) where
  hom := homReservoirDot T W.obj i m hP Z
  inv := homPreDotInverse T W.obj i m hP Z
  hom_inv_id := homPreDot_dotInverse T W.obj i m hP Z
  inv_hom_id := homPreDotInverse_dot T W.obj i m hP Z

/-- The negative probe cap has the literal Aut power used by the
central residual comparison. -/
theorem homPreNegativeCap_aut (r : ℕ)
    (Z : homWeightSector T.obj W.obj b m) :
    homPreNegativeCap T W.obj i m hP (r+1) Z =
      (homPreDotAut T W i hP ((homContentPreF T W.obj i m hP).obj Z) ^
        (-(r : ℤ)-1)).hom ≫
      (homContentPreAdjunction T W.obj T.leftAdjoints i m hP).counit.app Z := by
  have he : -((r+1 : ℕ) : ℤ) = -(r : ℤ)-1 := by omega
  dsimp only [homPreNegativeCap]
  rw [← he, ← aut_inv_power_eq_zpow]
  rfl

/-- The negative probe cup has the same literal negative Aut exponent
after applying the prescribed right adjoint. -/
theorem homPreNegativeCup_aut (r : ℕ)
    (Z : homWeightSector T.obj W.obj a m) :
    homPreNegativeCup T W.obj i m hP (r+1) Z =
      (homContentPreAdjunction T W.obj T.leftAdjoints i m hP).unit.app Z ≫
      (Functor.mapAut _ (homContentPreF T W.obj i m hP) (homPreDotAut T W i hP Z) ^
        (-(r : ℤ)-1)).hom := by
  have he : -((r+1 : ℕ) : ℤ) = -(r : ℤ)-1 := by omega
  dsimp only [homPreNegativeCup]
  rw [← he, ← map_aut_inv_power_eq_zpow]
  rfl

/-- The XP-to-YR ordered monomial is the negative probe cap followed by
the reservoir cup. The only interchange sign is one because the two
exponents are consecutive. -/
theorem homProbeToReservoir_monomial (r : ℕ)
    (Z : homWeightSector T.obj W.obj b m) :
    (homContentPostAdjunction T.obj W i β b hR).unit.app
        ((homContentPreE T W.obj i m hP).obj
          ((homContentPreF T W.obj i m hP).obj Z)) ≫
      (homContentPostF T.obj W i β b hR).map
        (homContentPostDot T.obj W i β b hR
          ((homContentPreE T W.obj i m hP).obj
            ((homContentPreF T W.obj i m hP).obj Z)) ^ r) ≫
      (homContentPostF T.obj W i β b hR).map
        ((homContentPostE T.obj W i β b hR).map
          (homPreDotInverse T W.obj i m hP
            ((homContentPreF T W.obj i m hP).obj Z) ^ (r+1))) ≫
      (homContentPostF T.obj W i β b hR).map
        ((homContentPostE T.obj W i β b hR).map
          ((homContentPreAdjunction T W.obj T.leftAdjoints i m hP).counit.app Z)) =
      homPreNegativeCap T W.obj i m hP (r+1) Z ≫
        homContentPostCup T.obj W i β b hR r Z := by
  have hn := (homContentPostCup_supernatural T.obj W i β b hR r).naturality
    ((homPreNegativeCap_supernatural T W.obj i m hP (r+1)).mem Z)
  rw [consecutive_parity, sign_zero, one_smul] at hn
  simpa only [homPreNegativeCap, homContentPostCup, Functor.id_map,
    Functor.id_obj, Functor.comp_obj, Functor.comp_map, Functor.map_comp,
    Category.assoc] using hn.symm

/-- The XR-to-YP ordered monomial separates into the reservoir cap and
negative probe cup. Moving the inverse probe power through the undotted
reservoir counit is even; the probe unit is an ordinary natural map. -/
theorem homReservoirToProbe_monomial (r : ℕ)
    (Z : homWeightSector T.obj W.obj a n) :
    (homContentPreAdjunction T W.obj T.leftAdjoints i n hP).unit.app
        ((homContentPostE T.obj W i β a hR).obj
          ((homContentPostF T.obj W i β a hR).obj Z)) ≫
      (homContentPreF T W.obj i n hP).map
        ((homContentPreE T W.obj i n hP).map
          (homContentPostDot T.obj W i β a hR
            ((homContentPostF T.obj W i β a hR).obj Z) ^ r)) ≫
      (homContentPreF T W.obj i n hP).map
        (homPreDotInverse T W.obj i n hP
          ((homContentPostE T.obj W i β a hR).obj
            ((homContentPostF T.obj W i β a hR).obj Z)) ^ (r+1)) ≫
      (homContentPreF T W.obj i n hP).map
        ((homContentPreE T W.obj i n hP).map
          ((homContentPostAdjunction T.obj W i β a hR).counit.app Z)) =
      homContentPostCap T.obj W i β a hR r Z ≫
        homPreNegativeCup T W.obj i n hP (r+1) Z := by
  have hn := (homPreDotInverse_power_supernatural T W.obj i n hP (r+1)).naturality
    (homContentPostAdjunction_counit_mem T.obj W i β a hR Z)
  simp only [mul_zero, sign_zero, one_smul, Functor.id_obj, Functor.comp_obj] at hn
  have hu := (homContentPreAdjunction T W.obj T.leftAdjoints i n hP).unit.naturality
    (homContentPostCap T.obj W i β a hR r Z)
  simp only [Functor.id_map, Functor.comp_map] at hu
  have hm := congrArg (homContentPreF T W.obj i n hP).map hn
  simp only [Functor.map_comp] at hm
  dsimp only [homPreNegativeCup]
  conv_rhs => rw [← Category.assoc, hu]
  simp only [homContentPostCap, Functor.map_comp, Category.assoc]
  rw [← hm]

end OddMath.SKM

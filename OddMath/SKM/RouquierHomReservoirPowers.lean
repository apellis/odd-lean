import OddMath.SKM.RouquierNormalizedHomAdjunction
import OddMath.SKM.RouquierMateSectors

/-!
# Reservoir dotted Hom coordinates

The cup and cap coordinate theorems prove `HomSectorTransport.md` §2 (5),
for every natural power of the raw dot. They supply the dotted window
coordinates for the Hom principal and central matrix comparisons; they do not
identify the principal inverse or prove the fusion comparison.
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
  (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)

/-- The raw reservoir dot, without a change of sign or transposition. -/
def homReservoirDot (Z : homWeightSector T.obj W muP muM) :
    End ((homContentPreE T W i muM h).obj Z) := T.dot i h ▷ Z

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Every raw power is supernatural on the full Hom space, including odd maps. -/
theorem homReservoirDot_power_naturality (n : ℕ)
    {Z Z' : homWeightSector T.obj W muP muM} {q : ZMod 2} {g : Z ⟶ Z'}
    (hg : g ∈ parity (R := k) _ _ q) :
    (homReservoirDot T W i muM h Z ^ n) ≫ T.E i h ◁ g =
      koszulSign ((n : ZMod 2) * D.parity i) q •
        (T.E i h ◁ g ≫ (homReservoirDot T W i muM h Z' ^ n)) := by
  simp only [homReservoirDot, whiskerRight_rouquierPower (k := k)]
  exact TwoSupercategory.super_interchange (rouquierPower_mem (T.dot_mem i h) n) hg

/-- Dotted unit of the specified normalized Hom adjunction. -/
def homReservoirCup (n : ℕ) (Z : homWeightSector T.obj W muP muM) :
    Z ⟶ (homContentPreF T W i muM h).obj ((homContentPreE T W i muM h).obj Z) :=
  (homContentPreAdjunction T W T.leftAdjoints i muM h).unit.app Z ≫
    (homContentPreF T W i muM h).map (homReservoirDot T W i muM h Z ^ n)

/-- Dotted counit of the same adjunction, with its fixed cap normalization. -/
def homReservoirCap (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreE T W i muM h).obj ((homContentPreF T W i muM h).obj Z) ⟶ Z :=
  (homReservoirDot T W i muM h ((homContentPreF T W i muM h).obj Z) ^ n) ≫
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z

/-- Removing the output shift costs exactly `(-1)^(σ n p)`. -/
theorem homReservoirCup_coordinates (n : ℕ) (Z : homWeightSector T.obj W muP muM) :
    homReservoirCup T W i muM h n Z ≫
      ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
        (T.F i h ≫ T.E i h ≫ Z)).hom =
    koszulSign (leftAdjParity D i (-nuP)) ((n : ZMod 2) * D.parity i) •
      ((leftUnitor Z).inv ≫ T.leftCup i h ▷ Z ≫
        (associator (T.F i h) (T.E i h) Z).hom ≫
        T.F i h ◁ (rouquierPower (T.dot i h) n ▷ Z)) := by
  rw [homReservoirCup, homContentPreAdjunction_leftAdjoints_unit_app]
  simp only [homReservoirDot, whiskerRight_rouquierPower (k := k),
    homContentPreF, Functor.comp_map, homPre, Category.assoc]
  rw [(homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_naturality
    (TwoSupercategory.whiskerLeft_mem (T.F i h)
      (TwoSupercategory.whiskerRight_mem Z (rouquierPower_mem (T.dot_mem i h) n)))]
  simp only [Linear.comp_smul, Iso.inv_hom_id_assoc]
  rw [koszulSign_smul (R := k)]

/-- The normalized cap coordinate has coefficient `(-1)^(σ(1+n p))`.
The inverse of `leftAdjScalar` remains on the raw cap at the source height. -/
theorem homReservoirCap_coordinates (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    homReservoirCap T W i muM h n Z =
    koszulSign (leftAdjParity D i (-nuP))
      (1 + (n : ZMod 2) * D.parity i) •
      (T.E i h ◁ ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
        (T.F i h ≫ Z)).hom ≫
        rouquierPower (T.dot i h) n ▷ (T.F i h ≫ Z) ≫
        (associator (T.E i h) (T.F i h) Z).inv ≫
        ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
        (leftUnitor Z).hom) := by
  rw [homReservoirCap, homContentPreAdjunction_leftAdjoints_counit_app]
  simp only [homReservoirDot, whiskerRight_rouquierPower (k := k),
    Preadditive.comp_zsmul, ← Category.assoc]
  dsimp only [homContentPreF, homContentPreE, Functor.comp_obj, homPre]
  rw [TwoSupercategory.super_interchange (rouquierPower_mem (T.dot_mem i h) n)
    ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_mem (T.F i h ≫ Z))]
  simp only [Preadditive.zsmul_comp, smul_smul, koszulSign_add_right, Category.assoc]
  rw [koszulSign_comm ((n : ZMod 2) * D.parity i)]
  have hs (σ : ZMod 2) : koszulSign σ σ = koszulSign σ 1 := by
    fin_cases σ <;> rfl
  rw [hs]

end OddMath.SKM
